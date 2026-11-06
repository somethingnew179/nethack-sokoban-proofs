import NetHack.Soko22Hazard87.AndIntroBlocks0317
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro79500 (p : Pattern) (ha : d208833 p = 1) (hb : d244487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208819 q = 1) (hb : d244473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208819, d244473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79474 q ha hb
    | true =>
      simp only [d208819, d244473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208820 q = 1) (hb : d244474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208820, d244474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208820, d244474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208821 q = 1) (hb : d244475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208821, d244475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208821, d244475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208822 q = 1) (hb : d244476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208822, d244476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208822, d244476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208823 q = 1) (hb : d244477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208823, d244477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208823, d244477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208833 q = 1) (hb : d244487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208833, d244487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208833, d244487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79501 (p : Pattern) (ha : d208853 p = 1) (hb : d244498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208839 q = 1) (hb : d244493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208839, d244493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208839, d244493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79480 q ha hb
  have h2 (q : Pattern) (ha : d208752 q = 1) (hb : d244406 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208752, d244406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79480 q ha hb
    | true =>
      simp only [d208752, d244406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208840 q = 1) (hb : d244494 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208840, d244494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208840, d244494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208753 q = 1) (hb : d244407 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208753, d244407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208753, d244407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208841 q = 1) (hb : d244495 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208841, d244495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208841, d244495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208842 q = 1) (hb : d244496 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208842, d244496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208842, d244496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d31957 q = 1) (hb : d208843 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31957, d208843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31957, d208843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79463 q ha hb
  have h8 (q : Pattern) (ha : d31756 q = 1) (hb : d208667 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31756, d208667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79463 q ha hb
    | true =>
      simp only [d31756, d208667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31958 q = 1) (hb : d208844 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31958, d208844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31958, d208844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31757 q = 1) (hb : d208668 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31757, d208668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31757, d208668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31959 q = 1) (hb : d208845 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31959, d208845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31959, d208845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31960 q = 1) (hb : d208846 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31960, d208846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31960, d208846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d208847 q = 1) (hb : d244497 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208847, d244497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208847, d244497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d31961 q = 1) (hb : d208848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
  have h15 (q : Pattern) (ha : d31643 q = 1) (hb : d208674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
    | true =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31962 q = 1) (hb : d208849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31644 q = 1) (hb : d208675 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31963 q = 1) (hb : d208850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31964 q = 1) (hb : d208851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31965 q = 1) (hb : d208852 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31965, d208852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31965, d208852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d208853 q = 1) (hb : d244498 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208853, d244498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208853, d244498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro79502 (p : Pattern) (ha : d208859 p = 1) (hb : d244504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31957 q = 1) (hb : d208843 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31957, d208843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31957, d208843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79463 q ha hb
  have h2 (q : Pattern) (ha : d31756 q = 1) (hb : d208667 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31756, d208667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79463 q ha hb
    | true =>
      simp only [d31756, d208667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31958 q = 1) (hb : d208844 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31958, d208844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31958, d208844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31757 q = 1) (hb : d208668 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31757, d208668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31757, d208668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31959 q = 1) (hb : d208845 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31959, d208845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31959, d208845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31960 q = 1) (hb : d208846 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31960, d208846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31960, d208846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31961 q = 1) (hb : d208848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
  have h8 (q : Pattern) (ha : d31643 q = 1) (hb : d208674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
    | true =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31962 q = 1) (hb : d208849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31644 q = 1) (hb : d208675 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31963 q = 1) (hb : d208850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31964 q = 1) (hb : d208851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31965 q = 1) (hb : d208852 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31965, d208852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31965, d208852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208854 q = 1) (hb : d244499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
  have h15 (q : Pattern) (ha : d208680 q = 1) (hb : d244336 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
    | true =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208855 q = 1) (hb : d244500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208681 q = 1) (hb : d244337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d208856 q = 1) (hb : d244501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d208857 q = 1) (hb : d244502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d208858 q = 1) (hb : d244503 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208858, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d208858, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d208859 q = 1) (hb : d244504 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208859, d244504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d208859, d244504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79503 (p : Pattern) (ha : d208864 p = 1) (hb : d244509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31961 q = 1) (hb : d208848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
  have h2 (q : Pattern) (ha : d31643 q = 1) (hb : d208674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
    | true =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31962 q = 1) (hb : d208849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31644 q = 1) (hb : d208675 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31963 q = 1) (hb : d208850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31964 q = 1) (hb : d208851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d208854 q = 1) (hb : d244499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
  have h8 (q : Pattern) (ha : d208680 q = 1) (hb : d244336 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
    | true =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208855 q = 1) (hb : d244500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208681 q = 1) (hb : d244337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d208856 q = 1) (hb : d244501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208857 q = 1) (hb : d244502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208858 q = 1) (hb : d244503 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208858, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d208858, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208863 q = 1) (hb : d244508 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208863, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208863, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208864 q = 1) (hb : d244509 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208864, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208864, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79504 (p : Pattern) (ha : d208869 p = 1) (hb : d244514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208854 q = 1) (hb : d244499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
  have h2 (q : Pattern) (ha : d208680 q = 1) (hb : d244336 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
    | true =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208855 q = 1) (hb : d244500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208681 q = 1) (hb : d244337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208856 q = 1) (hb : d244501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208857 q = 1) (hb : d244502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208863 q = 1) (hb : d244508 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208863, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208863, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1406 q = 1) (hb : d52894 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1406, d52894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1406, d52894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro154 q ha hb
  have h9 (q : Pattern) (ha : d1136 q = 1) (hb : d52717 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, d52717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro154 q ha hb
    | true =>
      simp only [d1136, d52717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1407 q = 1) (hb : d52895 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1407, d52895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1407, d52895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1137 q = 1) (hb : d52718 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, d52718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1137, d52718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1408 q = 1) (hb : d52896 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1408, d52896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1408, d52896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1409 q = 1) (hb : d52897 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1409, d52897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1409, d52897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1410 q = 1) (hb : d52898 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1410, d52898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1410, d52898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d208869 q = 1) (hb : d244514 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208869, d244514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208869, d244514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro79505 (p : Pattern) (ha : d208875 p = 1) (hb : d244520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208860 q = 1) (hb : d244505 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208860, d244505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79501 q ha hb
    | true =>
      simp only [d208860, d244505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79502 q ha hb
  have h2 (q : Pattern) (ha : d208861 q = 1) (hb : d244506 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208861, d244506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208861, d244506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208862 q = 1) (hb : d244507 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208862, d244507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208862, d244507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208865 q = 1) (hb : d244510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208865, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79502 q ha hb
    | true =>
      simp only [d208865, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
  have h5 (q : Pattern) (ha : d208866 q = 1) (hb : d244511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208866, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208866, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208867 q = 1) (hb : d244512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208867, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208867, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208868 q = 1) (hb : d244513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208868, d244513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208868, d244513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208870 q = 1) (hb : d244515 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
    | true =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79504 q ha hb
  have h9 (q : Pattern) (ha : d208871 q = 1) (hb : d244516 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208872 q = 1) (hb : d244517 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208873 q = 1) (hb : d244518 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208873, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208873, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208874 q = 1) (hb : d244519 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d208874, d244519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208874, d244519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208875 q = 1) (hb : d244520 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d208875, d244520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208875, d244520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79506 (p : Pattern) (ha : d208880 p = 1) (hb : d244525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208865 q = 1) (hb : d244510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208865, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79502 q ha hb
    | true =>
      simp only [d208865, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
  have h2 (q : Pattern) (ha : d208866 q = 1) (hb : d244511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208866, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208866, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208867 q = 1) (hb : d244512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208867, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208867, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208870 q = 1) (hb : d244515 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
    | true =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79504 q ha hb
  have h5 (q : Pattern) (ha : d208871 q = 1) (hb : d244516 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208872 q = 1) (hb : d244517 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208873 q = 1) (hb : d244518 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208873, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208873, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208878 q = 1) (hb : d244523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208878, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208878, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208879 q = 1) (hb : d244524 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d208879, d244524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208879, d244524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208880 q = 1) (hb : d244525 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d208880, d244525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208880, d244525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro79507 (p : Pattern) (ha : d208886 p = 1) (hb : d244531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208876 q = 1) (hb : d244521 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208876, d244521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79505 q ha hb
    | true =>
      simp only [d208876, d244521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208877 q = 1) (hb : d244522 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208877, d244522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208877, d244522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208881 q = 1) (hb : d244526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208881, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79506 q ha hb
    | true =>
      simp only [d208881, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208882 q = 1) (hb : d244527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208882, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208882, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208883 q = 1) (hb : d244528 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208883, d244528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208883, d244528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208884 q = 1) (hb : d244529 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208884, d244529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208884, d244529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208885 q = 1) (hb : d244530 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208885, d244530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208885, d244530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208886 q = 1) (hb : d244531 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d208886, d244531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208886, d244531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79508 (p : Pattern) (ha : d208888 p = 1) (hb : d244533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208870 q = 1) (hb : d244515 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
    | true =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79504 q ha hb
  have h2 (q : Pattern) (ha : d208871 q = 1) (hb : d244516 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208872 q = 1) (hb : d244517 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208878 q = 1) (hb : d244523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208878, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208878, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208887 q = 1) (hb : d244532 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d208887, d244532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208887, d244532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208888 q = 1) (hb : d244533 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d208888, d244533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208888, d244533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79509 (p : Pattern) (ha : d208894 p = 1) (hb : d244539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208881 q = 1) (hb : d244526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208881, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79506 q ha hb
    | true =>
      simp only [d208881, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208882 q = 1) (hb : d244527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208882, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208882, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208889 q = 1) (hb : d244534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208889, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79508 q ha hb
    | true =>
      simp only [d208889, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208890 q = 1) (hb : d244535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208890, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208890, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208891 q = 1) (hb : d244536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208891, d244536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208891, d244536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208892 q = 1) (hb : d244537 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208892, d244537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208892, d244537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208893 q = 1) (hb : d244538 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208893, d244538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208893, d244538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208894 q = 1) (hb : d244539 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d208894, d244539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208894, d244539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79510 (p : Pattern) (ha : d74316 p = 1) (hb : d244542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74310 q = 1) (hb : d244499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74310, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74310, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79484 q ha hb
  have h2 (q : Pattern) (ha : d74266 q = 1) (hb : d244336 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74266, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79484 q ha hb
    | true =>
      simp only [d74266, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74311 q = 1) (hb : d244500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74311, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74311, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74267 q = 1) (hb : d244337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74267, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74267, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74312 q = 1) (hb : d244501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74312, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74312, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74313 q = 1) (hb : d244502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74313, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74313, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d74314 q = 1) (hb : d244508 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74314, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74314, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d74316 q = 1) (hb : d244542 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74316, d244542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74316, d244542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79511 (p : Pattern) (ha : d208902 p = 1) (hb : d244509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31961 q = 1) (hb : d208848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31961, d208848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
  have h2 (q : Pattern) (ha : d31643 q = 1) (hb : d208674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79462 q ha hb
    | true =>
      simp only [d31643, d208674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31962 q = 1) (hb : d208849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31962, d208849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31644 q = 1) (hb : d208675 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31644, d208675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31963 q = 1) (hb : d208850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31963, d208850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31964 q = 1) (hb : d208851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31964, d208851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d208854 q = 1) (hb : d244499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208854, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
  have h8 (q : Pattern) (ha : d208680 q = 1) (hb : d244336 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79464 q ha hb
    | true =>
      simp only [d208680, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208855 q = 1) (hb : d244500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208855, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208681 q = 1) (hb : d244337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208681, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d208856 q = 1) (hb : d244501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208856, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208857 q = 1) (hb : d244502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d208857, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208858 q = 1) (hb : d244503 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208858, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d208858, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74310 q = 1) (hb : d244499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74310, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74310, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79484 q ha hb
  have h15 (q : Pattern) (ha : d74266 q = 1) (hb : d244336 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74266, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79484 q ha hb
    | true =>
      simp only [d74266, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74311 q = 1) (hb : d244500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74311, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74311, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74267 q = 1) (hb : d244337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74267, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74267, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74312 q = 1) (hb : d244501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74312, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74312, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74313 q = 1) (hb : d244502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74313, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74313, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74314 q = 1) (hb : d244508 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74314, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74314, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208902 q = 1) (hb : d244509 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208902, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208902, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79512 (p : Pattern) (ha : d208908 p = 1) (hb : d244548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208865 q = 1) (hb : d244510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208865, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79502 q ha hb
    | true =>
      simp only [d208865, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
  have h2 (q : Pattern) (ha : d208866 q = 1) (hb : d244511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208866, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208866, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208867 q = 1) (hb : d244512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208867, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208867, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208870 q = 1) (hb : d244515 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79503 q ha hb
    | true =>
      simp only [d208870, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79504 q ha hb
  have h5 (q : Pattern) (ha : d208871 q = 1) (hb : d244516 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208871, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208872 q = 1) (hb : d244517 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208872, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208873 q = 1) (hb : d244518 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208873, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208873, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208903 q = 1) (hb : d244543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208903, d244543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79511 q ha hb
    | true =>
      simp only [d208903, d244543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79510 q ha hb
  have h9 (q : Pattern) (ha : d208904 q = 1) (hb : d244544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208904, d244544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208904, d244544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208905 q = 1) (hb : d244545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208905, d244545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208905, d244545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208906 q = 1) (hb : d244546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208906, d244546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208906, d244546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208907 q = 1) (hb : d244547 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d208907, d244547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208907, d244547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208908 q = 1) (hb : d244548 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d208908, d244548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208908, d244548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79513 (p : Pattern) (ha : d208914 p = 1) (hb : d244554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208909 q = 1) (hb : d244549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208909, d244549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79512 q ha hb
    | true =>
      simp only [d208909, d244549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208910 q = 1) (hb : d244550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208910, d244550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208910, d244550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208911 q = 1) (hb : d244551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208911, d244551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208911, d244551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208912 q = 1) (hb : d244552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208912, d244552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208912, d244552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208913 q = 1) (hb : d244553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208913, d244553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208913, d244553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208914 q = 1) (hb : d244554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d208914, d244554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208914, d244554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79514 (p : Pattern) (ha : d208920 p = 1) (hb : d244560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208895 q = 1) (hb : d244540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208895, d244540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79507 q ha hb
    | true =>
      simp only [d208895, d244540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79509 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208900 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208901 q = 1) (hb : d244541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208901, d244541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208901, d244541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d208915 q = 1) (hb : d244555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208915, d244555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79513 q ha hb
    | true =>
      simp only [d208915, d244555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208916 q = 1) (hb : d244556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208916, d244556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208916, d244556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208917 q = 1) (hb : d244557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208917, d244557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208917, d244557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208918 q = 1) (hb : d244558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208918, d244558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208918, d244558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208919 q = 1) (hb : d244559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208919, d244559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208919, d244559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208920 q = 1) (hb : d244560 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208920, d244560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208920, d244560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79515 (p : Pattern) (ha : d208899 p = 1) (hb : d244565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208889 q = 1) (hb : d244534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208889, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79508 q ha hb
    | true =>
      simp only [d208889, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208890 q = 1) (hb : d244535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208890, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208890, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208896 q = 1) (hb : d244562 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208896, d244562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208896, d244562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208897 q = 1) (hb : d244563 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208897, d244563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208897, d244563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208898 q = 1) (hb : d244564 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208898, d244564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208898, d244564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208899 q = 1) (hb : d244565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d208899, d244565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208899, d244565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79516 (p : Pattern) (ha : d208927 p = 1) (hb : d244571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208922 q = 1) (hb : d244566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208922, d244566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79515 q ha hb
    | true =>
      simp only [d208922, d244566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208923 q = 1) (hb : d244567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208923, d244567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208923, d244567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208924 q = 1) (hb : d244568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208924, d244568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208924, d244568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208925 q = 1) (hb : d244569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208925, d244569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208925, d244569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208926 q = 1) (hb : d244570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208926, d244570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208926, d244570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208927 q = 1) (hb : d244571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208927, d244571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208927, d244571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79517 (p : Pattern) (ha : d208933 p = 1) (hb : d244577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208719 q = 1) (hb : d244375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208719, d244375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208719, d244375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79472 q ha hb
  have h2 (q : Pattern) (ha : d208720 q = 1) (hb : d244376 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208720, d244376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208720, d244376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208729 q = 1) (hb : d244385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208729, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79472 q ha hb
    | true =>
      simp only [d208729, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79475 q ha hb
  have h4 (q : Pattern) (ha : d208730 q = 1) (hb : d244386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208730, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208730, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208731 q = 1) (hb : d244387 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208731, d244387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208731, d244387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208812 q = 1) (hb : d244466 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208812, d244466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79489 q ha hb
    | true =>
      simp only [d208812, d244466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79496 q ha hb
  have h7 (q : Pattern) (ha : d208825 q = 1) (hb : d244479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208825, d244479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79497 q ha hb
    | true =>
      simp only [d208825, d244479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79498 q ha hb
  have h8 (q : Pattern) (ha : d208826 q = 1) (hb : d244480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208826, d244480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208826, d244480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208827 q = 1) (hb : d244481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208827, d244481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208827, d244481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208828 q = 1) (hb : d244482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208828, d244482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208828, d244482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208832 q = 1) (hb : d244486 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208832, d244486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208832, d244486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79499 q ha hb
  have h12 (q : Pattern) (ha : d208834 q = 1) (hb : d244488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208834, d244488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208834, d244488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79500 q ha hb
  have h13 (q : Pattern) (ha : d208835 q = 1) (hb : d244489 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208835, d244489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d208835, d244489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208836 q = 1) (hb : d244490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208836, d244490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208836, d244490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208837 q = 1) (hb : d244491 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208837, d244491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d208837, d244491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208838 q = 1) (hb : d244492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208838, d244492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208838, d244492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208921 q = 1) (hb : d244561 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208921, d244561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208921, d244561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79514 q ha hb
  have h18 (q : Pattern) (ha : d208928 q = 1) (hb : d244572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208928, d244572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208928, d244572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79516 q ha hb
  have h19 (q : Pattern) (ha : d208929 q = 1) (hb : d244573 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208929, d244573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208929, d244573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d208930 q = 1) (hb : d244574 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208930, d244574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d208930, d244574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208931 q = 1) (hb : d244575 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208931, d244575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d208931, d244575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208932 q = 1) (hb : d244576 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208932, d244576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d208932, d244576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208933 q = 1) (hb : d244577 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208933, d244577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208933, d244577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro79518 (p : Pattern) (ha : d208939 p = 1) (hb : d244583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208934 q = 1) (hb : d244578 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208934, d244578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208934, d244578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79517 q ha hb
  have h2 (q : Pattern) (ha : d208935 q = 1) (hb : d244579 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208935, d244579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208935, d244579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208936 q = 1) (hb : d244580 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208936, d244580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208936, d244580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208937 q = 1) (hb : d244581 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208937, d244581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208937, d244581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208938 q = 1) (hb : d244582 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208938, d244582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208938, d244582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208939 q = 1) (hb : d244583 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208939, d244583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208939, d244583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79519 (p : Pattern) (ha : d32171 p = 1) (hb : d208954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31303 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75017 q ha hb
    | true =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31304 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32166 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32166, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32166, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32167 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32167, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32167, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32168 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32168, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32168, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32169 q = 1) (hb : d208945 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32169, d208945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32169, d208945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32170 q = 1) (hb : d208946 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32170, d208946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32170, d208946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h12 (q : Pattern) (ha : d32154 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32154, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75020 q ha hb
  have h13 (q : Pattern) (ha : d32155 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32155, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35563 q ha hb
  have h14 (q : Pattern) (ha : d32156 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32156, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d25765 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d25766 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25766, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32157 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32157, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d32158 q = 1) (hb : d208952 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d208952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32158, d208952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d32159 q = 1) (hb : d208953 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d208953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d32159, d208953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d32171 q = 1) (hb : d208954 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32171, d208954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32171, d208954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro79520 (p : Pattern) (ha : d32273 p = 1) (hb : d208947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31303 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75017 q ha hb
    | true =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31304 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31736 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31736, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31736, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31737 q = 1) (hb : d208943 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31737, d208943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31737, d208943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31738 q = 1) (hb : d208944 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31738, d208944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31738, d208944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32166 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32166, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32166, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32167 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32167, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32167, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32168 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32168, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32168, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32169 q = 1) (hb : d208945 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32169, d208945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32169, d208945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d32170 q = 1) (hb : d208946 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32170, d208946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32170, d208946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h16 (q : Pattern) (ha : d32273 q = 1) (hb : d208947 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32273, d208947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32273, d208947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79521 (p : Pattern) (ha : d208962 p = 1) (hb : d244587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d32154 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32154, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75020 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35563 q ha hb
  have h3 (q : Pattern) (ha : d32156 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32156, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25765 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25766 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25766, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32157 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32157, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32158 q = 1) (hb : d208952 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d208952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32158, d208952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d32159 q = 1) (hb : d208953 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d208953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32159, d208953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h12 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h13 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d1577 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24324 q = 1) (hb : d208960 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24324, d208960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24324, d208960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d24325 q = 1) (hb : d208961 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24325, d208961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d24325, d208961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d208962 q = 1) (hb : d244587 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d208962, d244587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208962, d244587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro79522 (p : Pattern) (ha : d208968 p = 1) (hb : d244593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32274 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79520 q ha hb
    | true =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32275 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32276 q = 1) (hb : d208950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32276, d208950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32276, d208950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32277 q = 1) (hb : d208951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32277, d208951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32277, d208951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32174 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32175 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32279 q = 1) (hb : d208959 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32279, d208959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32279, d208959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208965 q = 1) (hb : d244590 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208966 q = 1) (hb : d244591 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208967 q = 1) (hb : d244592 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208967, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d208967, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208968 q = 1) (hb : d244593 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208968, d244593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208968, d244593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79523 (p : Pattern) (ha : d208970 p = 1) (hb : d244595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32174 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32175 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208965 q = 1) (hb : d244590 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208966 q = 1) (hb : d244591 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208967 q = 1) (hb : d244592 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208967, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208967, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208969 q = 1) (hb : d244594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208969, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208969, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d208970 q = 1) (hb : d244595 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208970, d244595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208970, d244595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79524 (p : Pattern) (ha : d208974 p = 1) (hb : d244599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208965 q = 1) (hb : d244590 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208966 q = 1) (hb : d244591 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208969 q = 1) (hb : d244594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208969, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208969, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d1597 q = 1) (hb : d53038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
    | true =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1598 q = 1) (hb : d53039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1599 q = 1) (hb : d53040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1599, d53040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1599, d53040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1600 q = 1) (hb : d53041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1600, d53041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1600, d53041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1601 q = 1) (hb : d53042 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1601, d53042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1601, d53042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d208974 q = 1) (hb : d244599 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d208974, d244599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208974, d244599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro79525 (p : Pattern) (ha : d208981 p = 1) (hb : d244606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208971 q = 1) (hb : d244596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208971, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79522 q ha hb
    | true =>
      simp only [d208971, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
  have h2 (q : Pattern) (ha : d208972 q = 1) (hb : d244597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208972, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208972, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208973 q = 1) (hb : d244598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208973, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208973, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208975 q = 1) (hb : d244600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
    | true =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79524 q ha hb
  have h5 (q : Pattern) (ha : d208976 q = 1) (hb : d244601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208977 q = 1) (hb : d244602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208978 q = 1) (hb : d244603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208978, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208978, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208979 q = 1) (hb : d244604 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208979, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208979, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208980 q = 1) (hb : d244605 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d208980, d244605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208980, d244605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208981 q = 1) (hb : d244606 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d208981, d244606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208981, d244606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro79526 (p : Pattern) (ha : d208985 p = 1) (hb : d244610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208975 q = 1) (hb : d244600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
    | true =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79524 q ha hb
  have h2 (q : Pattern) (ha : d208976 q = 1) (hb : d244601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208977 q = 1) (hb : d244602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208979 q = 1) (hb : d244604 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208979, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208979, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208984 q = 1) (hb : d244609 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d208984, d244609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208984, d244609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208985 q = 1) (hb : d244610 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d208985, d244610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208985, d244610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79527 (p : Pattern) (ha : d208991 p = 1) (hb : d244616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d244613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208989 q = 1) (hb : d244614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208990 q = 1) (hb : d244615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208990, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208990, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208991 q = 1) (hb : d244616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d208991, d244616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208991, d244616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79528 (p : Pattern) (ha : d208995 p = 1) (hb : d244620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d244617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208993 q = 1) (hb : d244618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208994 q = 1) (hb : d244619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208994, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208994, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208995 q = 1) (hb : d244620 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d208995, d244620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208995, d244620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79529 (p : Pattern) (ha : d209001 p = 1) (hb : d244626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208996 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
    | true =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
  have h2 (q : Pattern) (ha : d208997 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208997, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208997, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208998 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208998, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208998, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208999 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208999, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208999, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209000 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209000, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209000, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209001 q = 1) (hb : d244626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209001, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209001, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79530 (p : Pattern) (ha : d209004 p = 1) (hb : d244629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d244613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208989 q = 1) (hb : d244614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208990 q = 1) (hb : d244615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208990, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208990, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209004 q = 1) (hb : d244629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209004, d244629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209004, d244629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79531 (p : Pattern) (ha : d209005 p = 1) (hb : d244630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d244617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208993 q = 1) (hb : d244618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208994 q = 1) (hb : d244619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d208994, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208994, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209005 q = 1) (hb : d244630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209005, d244630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209005, d244630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79532 (p : Pattern) (ha : d209011 p = 1) (hb : d244636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208996 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
    | true =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
  have h2 (q : Pattern) (ha : d208997 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208997, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208997, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208998 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208998, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208998, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208999 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208999, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208999, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209000 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209000, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209000, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209006 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79530 q ha hb
    | true =>
      simp only [d209006, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79531 q ha hb
  have h7 (q : Pattern) (ha : d209007 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209007, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209007, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209008 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209008, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209008, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209009 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209009, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209009, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209010 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209010, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209010, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209011 q = 1) (hb : d244636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209011, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209011, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79533 (p : Pattern) (ha : d209016 p = 1) (hb : d244641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d244613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208989 q = 1) (hb : d244614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209015 q = 1) (hb : d244640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209015, d244640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209015, d244640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209016 q = 1) (hb : d244641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209016, d244641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209016, d244641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79534 (p : Pattern) (ha : d209018 p = 1) (hb : d244643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d244617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208993 q = 1) (hb : d244618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209017 q = 1) (hb : d244642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209017, d244642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209017, d244642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209018 q = 1) (hb : d244643 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209018, d244643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209018, d244643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79535 (p : Pattern) (ha : d209025 p = 1) (hb : d244650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d244613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209023 q = 1) (hb : d244648 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209023, d244648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209023, d244648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209024 q = 1) (hb : d244649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209024, d244649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209024, d244649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209025 q = 1) (hb : d244650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209025, d244650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209025, d244650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79536 (p : Pattern) (ha : d209028 p = 1) (hb : d244653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d244617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209026 q = 1) (hb : d244651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209026, d244651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209026, d244651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209027 q = 1) (hb : d244652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209027, d244652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209027, d244652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209028 q = 1) (hb : d244653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209028, d244653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209028, d244653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79537 (p : Pattern) (ha : d32268 p = 1) (hb : d209034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31303 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75017 q ha hb
    | true =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31304 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31736 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31736, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31736, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31737 q = 1) (hb : d208943 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31737, d208943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31737, d208943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31738 q = 1) (hb : d208944 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31738, d208944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31738, d208944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d32268 q = 1) (hb : d209034 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32268, d209034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32268, d209034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79538 (p : Pattern) (ha : d32280 p = 1) (hb : d209040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32269 q = 1) (hb : d209035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32269, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79537 q ha hb
    | true =>
      simp only [d32269, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32270 q = 1) (hb : d209036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32270, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32270, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32271 q = 1) (hb : d209037 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32271, d209037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32271, d209037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32272 q = 1) (hb : d209038 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32272, d209038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32272, d209038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32274 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79520 q ha hb
    | true =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32275 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32276 q = 1) (hb : d208950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32276, d208950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32276, d208950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32277 q = 1) (hb : d208951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32277, d208951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32277, d208951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32278 q = 1) (hb : d209039 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32278, d209039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32278, d209039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32174 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32175 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32279 q = 1) (hb : d208959 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32279, d208959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32279, d208959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32280 q = 1) (hb : d209040 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32280, d209040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32280, d209040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79539 (p : Pattern) (ha : d209046 p = 1) (hb : d244662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209041 q = 1) (hb : d244657 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209041, d244657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79538 q hb ha
    | true =>
      simp only [d209041, d244657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79522 q ha hb
  have h2 (q : Pattern) (ha : d209042 q = 1) (hb : d244658 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209042, d244658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209042, d244658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209043 q = 1) (hb : d244659 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209043, d244659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209043, d244659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208971 q = 1) (hb : d244596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208971, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79522 q ha hb
    | true =>
      simp only [d208971, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
  have h5 (q : Pattern) (ha : d208972 q = 1) (hb : d244597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208972, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208972, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208973 q = 1) (hb : d244598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208973, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208973, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209044 q = 1) (hb : d244660 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209044, d244660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209044, d244660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208975 q = 1) (hb : d244600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
    | true =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79524 q ha hb
  have h9 (q : Pattern) (ha : d208976 q = 1) (hb : d244601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208977 q = 1) (hb : d244602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208978 q = 1) (hb : d244603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208978, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208978, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209045 q = 1) (hb : d244661 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209045, d244661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209045, d244661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209046 q = 1) (hb : d244662 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209046, d244662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209046, d244662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79540 (p : Pattern) (ha : d209052 p = 1) (hb : d244668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209047 q = 1) (hb : d244663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209047, d244663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79539 q ha hb
    | true =>
      simp only [d209047, d244663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209048 q = 1) (hb : d244664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209048, d244664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209048, d244664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209049 q = 1) (hb : d244665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209049, d244665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209049, d244665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209050 q = 1) (hb : d244666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209050, d244666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209050, d244666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209051 q = 1) (hb : d244667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209051, d244667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209051, d244667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209052 q = 1) (hb : d244668 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209052, d244668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209052, d244668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79541 (p : Pattern) (ha : d74355 p = 1) (hb : d244671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d32154 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32154, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75020 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35563 q ha hb
  have h3 (q : Pattern) (ha : d32156 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32156, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32157 q = 1) (hb : d74350 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d74350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32157, d74350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32158 q = 1) (hb : d74351 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d74351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32158, d74351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d32159 q = 1) (hb : d74352 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d74352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32159, d74352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h10 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5627 q = 1) (hb : d74353 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5627, d74353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5627, d74353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d5628 q = 1) (hb : d74354 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5628, d74354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5628, d74354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d74355 q = 1) (hb : d244671 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d74355, d244671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74355, d244671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro79542 (p : Pattern) (ha : d74362 p = 1) (hb : d244678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74356 q = 1) (hb : d244672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79541 q ha hb
    | true =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74357 q = 1) (hb : d244673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74358 q = 1) (hb : d244674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74358, d244674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74358, d244674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74359 q = 1) (hb : d244675 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74359, d244675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74359, d244675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74360 q = 1) (hb : d244676 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74360, d244676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74360, d244676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74362 q = 1) (hb : d244678 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74362, d244678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74362, d244678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79543 (p : Pattern) (ha : d209055 p = 1) (hb : d244677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32174 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32174, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32175 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32175, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208965 q = 1) (hb : d244590 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208965, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208966 q = 1) (hb : d244591 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208966, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208967 q = 1) (hb : d244592 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208967, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208967, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74356 q = 1) (hb : d244672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79541 q ha hb
    | true =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74357 q = 1) (hb : d244673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74358 q = 1) (hb : d244674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74358, d244674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74358, d244674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74359 q = 1) (hb : d244675 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74359, d244675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74359, d244675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74360 q = 1) (hb : d244676 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74360, d244676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74360, d244676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209055 q = 1) (hb : d244677 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209055, d244677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209055, d244677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79544 (p : Pattern) (ha : d209061 p = 1) (hb : d244684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208971 q = 1) (hb : d244596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208971, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79522 q ha hb
    | true =>
      simp only [d208971, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
  have h2 (q : Pattern) (ha : d208972 q = 1) (hb : d244597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208972, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208972, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208973 q = 1) (hb : d244598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208973, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208973, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208975 q = 1) (hb : d244600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79523 q ha hb
    | true =>
      simp only [d208975, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79524 q ha hb
  have h5 (q : Pattern) (ha : d208976 q = 1) (hb : d244601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208976, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208977 q = 1) (hb : d244602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208977, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208978 q = 1) (hb : d244603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208978, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208978, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209056 q = 1) (hb : d244679 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209056, d244679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79543 q ha hb
    | true =>
      simp only [d209056, d244679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79542 q ha hb
  have h9 (q : Pattern) (ha : d209057 q = 1) (hb : d244680 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209057, d244680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209057, d244680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209058 q = 1) (hb : d244681 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209058, d244681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209058, d244681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209059 q = 1) (hb : d244682 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209059, d244682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209059, d244682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209060 q = 1) (hb : d244683 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209060, d244683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209060, d244683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209061 q = 1) (hb : d244684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209061, d244684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209061, d244684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79545 (p : Pattern) (ha : d209067 p = 1) (hb : d244690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209062 q = 1) (hb : d244685 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209062, d244685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79544 q ha hb
    | true =>
      simp only [d209062, d244685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209063 q = 1) (hb : d244686 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209063, d244686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209063, d244686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209064 q = 1) (hb : d244687 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209064, d244687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209064, d244687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209065 q = 1) (hb : d244688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209065, d244688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209065, d244688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209066 q = 1) (hb : d244689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209066, d244689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209066, d244689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209067 q = 1) (hb : d244690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209067, d244690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209067, d244690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79546 (p : Pattern) (ha : d209073 p = 1) (hb : d244696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209019 q = 1) (hb : d244644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209019, d244644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79533 q ha hb
    | true =>
      simp only [d209019, d244644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79534 q ha hb
  have h2 (q : Pattern) (ha : d209020 q = 1) (hb : d244645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209020, d244645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209020, d244645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209021 q = 1) (hb : d244646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209021, d244646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209021, d244646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209022 q = 1) (hb : d244647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209022, d244647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209022, d244647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209029 q = 1) (hb : d244654 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209029, d244654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79535 q ha hb
    | true =>
      simp only [d209029, d244654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79536 q ha hb
  have h6 (q : Pattern) (ha : d209030 q = 1) (hb : d244655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209030, d244655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209030, d244655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209031 q = 1) (hb : d244656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209031, d244656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209031, d244656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209053 q = 1) (hb : d244669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209053, d244669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79540 q ha hb
    | true =>
      simp only [d209053, d244669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209054 q = 1) (hb : d244670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d244670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209054, d244670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209068 q = 1) (hb : d244691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209068, d244691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79545 q ha hb
    | true =>
      simp only [d209068, d244691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209069 q = 1) (hb : d244692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209069, d244692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209069, d244692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209070 q = 1) (hb : d244693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d244693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209070, d244693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209071 q = 1) (hb : d244694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d244694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209071, d244694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209072 q = 1) (hb : d244695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d244695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209072, d244695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209073 q = 1) (hb : d244696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209073, d244696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209073, d244696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79547 (p : Pattern) (ha : d209074 p = 1) (hb : d244697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d244613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208989 q = 1) (hb : d244614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208989, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209015 q = 1) (hb : d244640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209015, d244640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209015, d244640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209074 q = 1) (hb : d244697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209074, d244697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209074, d244697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79548 (p : Pattern) (ha : d209075 p = 1) (hb : d244698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d244617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208993 q = 1) (hb : d244618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208993, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209017 q = 1) (hb : d244642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209017, d244642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209017, d244642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209075 q = 1) (hb : d244698 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209075, d244698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209075, d244698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79549 (p : Pattern) (ha : d209080 p = 1) (hb : d244703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d244613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209023 q = 1) (hb : d244648 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209023, d244648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209023, d244648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209024 q = 1) (hb : d244649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209024, d244649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209024, d244649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209080 q = 1) (hb : d244703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209080, d244703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209080, d244703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79550 (p : Pattern) (ha : d209081 p = 1) (hb : d244704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d244611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79526 q ha hb
    | true =>
      simp only [d208986, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d244612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d244617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209026 q = 1) (hb : d244651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209026, d244651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209026, d244651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209027 q = 1) (hb : d244652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209027, d244652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209027, d244652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209081 q = 1) (hb : d244704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209081, d244704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209081, d244704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79551 (p : Pattern) (ha : d209085 p = 1) (hb : d244708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209047 q = 1) (hb : d244663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209047, d244663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79539 q ha hb
    | true =>
      simp only [d209047, d244663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209048 q = 1) (hb : d244664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209048, d244664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209048, d244664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208982 q = 1) (hb : d244607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79525 q ha hb
    | true =>
      simp only [d208982, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208983 q = 1) (hb : d244608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209049 q = 1) (hb : d244665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209049, d244665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209049, d244665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209050 q = 1) (hb : d244666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209050, d244666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209050, d244666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209051 q = 1) (hb : d244667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209051, d244667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209051, d244667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209085 q = 1) (hb : d244708 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209085, d244708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209085, d244708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79552 (p : Pattern) (ha : d209088 p = 1) (hb : d244711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209062 q = 1) (hb : d244685 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209062, d244685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79544 q ha hb
    | true =>
      simp only [d209062, d244685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209063 q = 1) (hb : d244686 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209063, d244686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209063, d244686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209064 q = 1) (hb : d244687 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209064, d244687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209064, d244687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209065 q = 1) (hb : d244688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209065, d244688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209065, d244688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209066 q = 1) (hb : d244689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209066, d244689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209066, d244689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209088 q = 1) (hb : d244711 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209088, d244711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209088, d244711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79553 (p : Pattern) (ha : d209094 p = 1) (hb : d244717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209019 q = 1) (hb : d244644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209019, d244644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79533 q ha hb
    | true =>
      simp only [d209019, d244644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79534 q ha hb
  have h2 (q : Pattern) (ha : d209020 q = 1) (hb : d244645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209020, d244645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209020, d244645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209021 q = 1) (hb : d244646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209021, d244646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209021, d244646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209022 q = 1) (hb : d244647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209022, d244647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209022, d244647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209029 q = 1) (hb : d244654 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209029, d244654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79535 q ha hb
    | true =>
      simp only [d209029, d244654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79536 q ha hb
  have h6 (q : Pattern) (ha : d209030 q = 1) (hb : d244655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209030, d244655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209030, d244655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209031 q = 1) (hb : d244656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209031, d244656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209031, d244656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209053 q = 1) (hb : d244669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209053, d244669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79540 q ha hb
    | true =>
      simp only [d209053, d244669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209054 q = 1) (hb : d244670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d244670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209054, d244670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209068 q = 1) (hb : d244691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209068, d244691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79545 q ha hb
    | true =>
      simp only [d209068, d244691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209069 q = 1) (hb : d244692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209069, d244692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209069, d244692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209070 q = 1) (hb : d244693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d244693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209070, d244693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209071 q = 1) (hb : d244694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d244694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209071, d244694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209072 q = 1) (hb : d244695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d244695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209072, d244695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209076 q = 1) (hb : d244699 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209076, d244699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79547 q ha hb
    | true =>
      simp only [d209076, d244699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79548 q ha hb
  have h17 (q : Pattern) (ha : d209077 q = 1) (hb : d244700 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209077, d244700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209077, d244700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209078 q = 1) (hb : d244701 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209078, d244701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209078, d244701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d209079 q = 1) (hb : d244702 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209079, d244702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209079, d244702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209082 q = 1) (hb : d244705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209082, d244705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79549 q ha hb
    | true =>
      simp only [d209082, d244705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79550 q ha hb
  have h21 (q : Pattern) (ha : d209083 q = 1) (hb : d244706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209083, d244706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209083, d244706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d209084 q = 1) (hb : d244707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209084, d244707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209084, d244707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209086 q = 1) (hb : d244709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209086, d244709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79551 q ha hb
    | true =>
      simp only [d209086, d244709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79530 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209087 q = 1) (hb : d244710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d244710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d209087, d244710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d209089 q = 1) (hb : d244712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209089, d244712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79552 q ha hb
    | true =>
      simp only [d209089, d244712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d209090 q = 1) (hb : d244713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209090, d244713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d209090, d244713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d209091 q = 1) (hb : d244714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d244714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209091, d244714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d209092 q = 1) (hb : d244715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209092, d244715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d209092, d244715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209093 q = 1) (hb : d244716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209093, d244716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209093, d244716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209094 q = 1) (hb : d244717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209094, d244717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209094, d244717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro79554 (p : Pattern) (ha : d209101 p = 1) (hb : d244724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208996 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
    | true =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
  have h2 (q : Pattern) (ha : d208997 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208997, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208997, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208998 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208998, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208998, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208999 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208999, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208999, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209000 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209000, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209000, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209096 q = 1) (hb : d244719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209096, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
    | true =>
      simp only [d209096, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209097 q = 1) (hb : d244720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209097, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209097, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209098 q = 1) (hb : d244721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209098, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209098, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209099 q = 1) (hb : d244722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209099, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209099, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209100 q = 1) (hb : d244723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209100, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209100, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209101 q = 1) (hb : d244724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209101, d244724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209101, d244724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79555 (p : Pattern) (ha : d209107 p = 1) (hb : d244730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209096 q = 1) (hb : d244719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209096, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
    | true =>
      simp only [d209096, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209097 q = 1) (hb : d244720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209097, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209097, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209098 q = 1) (hb : d244721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209098, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209098, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209099 q = 1) (hb : d244722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209099, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209099, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209100 q = 1) (hb : d244723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209100, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209100, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209102 q = 1) (hb : d244725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209102, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79531 q ha hb
    | true =>
      simp only [d209102, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209103 q = 1) (hb : d244726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209103, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209103, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209104 q = 1) (hb : d244727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209104, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209104, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209105 q = 1) (hb : d244728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209105, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209105, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209106 q = 1) (hb : d244729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209106, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209106, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209107 q = 1) (hb : d244730 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209107, d244730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209107, d244730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79556 (p : Pattern) (ha : d209114 p = 1) (hb : d244737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209086 q = 1) (hb : d244709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209086, d244709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79551 q ha hb
    | true =>
      simp only [d209086, d244709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79530 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209087 q = 1) (hb : d244710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d244710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209087, d244710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209089 q = 1) (hb : d244712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209089, d244712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79552 q ha hb
    | true =>
      simp only [d209089, d244712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209090 q = 1) (hb : d244713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209090, d244713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209090, d244713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209091 q = 1) (hb : d244714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d244714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209091, d244714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209112 q = 1) (hb : d244735 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209112, d244735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209112, d244735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209113 q = 1) (hb : d244736 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209113, d244736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209113, d244736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209114 q = 1) (hb : d244737 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d244737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d244737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79557 (p : Pattern) (ha : d209116 p = 1) (hb : d244739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209102 q = 1) (hb : d244725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209102, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79531 q ha hb
    | true =>
      simp only [d209102, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209103 q = 1) (hb : d244726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209103, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209103, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209104 q = 1) (hb : d244727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209104, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209104, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209105 q = 1) (hb : d244728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209105, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209105, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209106 q = 1) (hb : d244729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209106, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209106, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209116 q = 1) (hb : d244739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209116, d244739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209116, d244739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79558 (p : Pattern) (ha : d32501 p = 1) (hb : d209136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32487 q = 1) (hb : d209122 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32487, d209122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32487, d209122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79537 q ha hb
  have h2 (q : Pattern) (ha : d32269 q = 1) (hb : d209035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32269, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79537 q ha hb
    | true =>
      simp only [d32269, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32488 q = 1) (hb : d209123 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32488, d209123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32488, d209123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32270 q = 1) (hb : d209036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32270, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32270, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32489 q = 1) (hb : d209124 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32489, d209124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32489, d209124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32490 q = 1) (hb : d209125 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32490, d209125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32490, d209125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32491 q = 1) (hb : d209126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32491, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32491, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79520 q ha hb
  have h8 (q : Pattern) (ha : d32274 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79520 q ha hb
    | true =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32492 q = 1) (hb : d209127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32492, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32492, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32275 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32493 q = 1) (hb : d209128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32493, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32493, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32494 q = 1) (hb : d209129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32494, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32494, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32495 q = 1) (hb : d209130 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32495, d209130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32495, d209130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32496 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
  have h15 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32497 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32498 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32499 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d32500 q = 1) (hb : d209135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32500, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32500, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d32501 q = 1) (hb : d209136 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32501, d209136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32501, d209136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79559 (p : Pattern) (ha : d209142 p = 1) (hb : d244750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32491 q = 1) (hb : d209126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32491, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32491, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79520 q ha hb
  have h2 (q : Pattern) (ha : d32274 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79520 q ha hb
    | true =>
      simp only [d32274, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32492 q = 1) (hb : d209127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32492, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32492, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32275 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32275, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32493 q = 1) (hb : d209128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32493, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32493, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32494 q = 1) (hb : d209129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32494, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32494, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32496 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
  have h8 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32497 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32498 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32499 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32500 q = 1) (hb : d209135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32500, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32500, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209137 q = 1) (hb : d244745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
  have h15 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209138 q = 1) (hb : d244746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d209139 q = 1) (hb : d244747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d209140 q = 1) (hb : d244748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d209141 q = 1) (hb : d244749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209141, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d209141, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d209142 q = 1) (hb : d244750 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209142, d244750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d209142, d244750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79560 (p : Pattern) (ha : d209147 p = 1) (hb : d244755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32496 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
  have h2 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32497 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32498 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32499 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209137 q = 1) (hb : d244745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
  have h8 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209138 q = 1) (hb : d244746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209139 q = 1) (hb : d244747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209140 q = 1) (hb : d244748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209141 q = 1) (hb : d244749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209141, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209141, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209146 q = 1) (hb : d244754 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209146, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209146, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209147 q = 1) (hb : d244755 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209147, d244755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209147, d244755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79561 (p : Pattern) (ha : d209152 p = 1) (hb : d244760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209137 q = 1) (hb : d244745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
  have h2 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209138 q = 1) (hb : d244746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209139 q = 1) (hb : d244747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209140 q = 1) (hb : d244748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209146 q = 1) (hb : d244754 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209146, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209146, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1883 q = 1) (hb : d53209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
  have h9 (q : Pattern) (ha : d1597 q = 1) (hb : d53038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
    | true =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1884 q = 1) (hb : d53210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1598 q = 1) (hb : d53039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1885 q = 1) (hb : d53211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1886 q = 1) (hb : d53212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1887 q = 1) (hb : d53213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d209152 q = 1) (hb : d244760 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209152, d244760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209152, d244760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro79562 (p : Pattern) (ha : d209158 p = 1) (hb : d244766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209143 q = 1) (hb : d244751 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209143, d244751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79558 q hb ha
    | true =>
      simp only [d209143, d244751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79559 q ha hb
  have h2 (q : Pattern) (ha : d209144 q = 1) (hb : d244752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209144, d244752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209144, d244752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209145 q = 1) (hb : d244753 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209145, d244753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209145, d244753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209148 q = 1) (hb : d244756 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209148, d244756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79559 q ha hb
    | true =>
      simp only [d209148, d244756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
  have h5 (q : Pattern) (ha : d209149 q = 1) (hb : d244757 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209149, d244757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209149, d244757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209150 q = 1) (hb : d244758 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209150, d244758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209150, d244758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209151 q = 1) (hb : d244759 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209151, d244759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209151, d244759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209153 q = 1) (hb : d244761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
    | true =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79561 q ha hb
  have h9 (q : Pattern) (ha : d209154 q = 1) (hb : d244762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209155 q = 1) (hb : d244763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209156 q = 1) (hb : d244764 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209156, d244764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209156, d244764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209157 q = 1) (hb : d244765 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209157, d244765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209157, d244765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209158 q = 1) (hb : d244766 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209158, d244766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209158, d244766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79563 (p : Pattern) (ha : d209163 p = 1) (hb : d244771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209148 q = 1) (hb : d244756 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209148, d244756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79559 q ha hb
    | true =>
      simp only [d209148, d244756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
  have h2 (q : Pattern) (ha : d209149 q = 1) (hb : d244757 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209149, d244757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209149, d244757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209150 q = 1) (hb : d244758 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209150, d244758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209150, d244758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209153 q = 1) (hb : d244761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
    | true =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79561 q ha hb
  have h5 (q : Pattern) (ha : d209154 q = 1) (hb : d244762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209155 q = 1) (hb : d244763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209156 q = 1) (hb : d244764 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209156, d244764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209156, d244764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209161 q = 1) (hb : d244769 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209161, d244769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209161, d244769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209162 q = 1) (hb : d244770 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209162, d244770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209162, d244770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209163 q = 1) (hb : d244771 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209163, d244771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209163, d244771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro79564 (p : Pattern) (ha : d209169 p = 1) (hb : d244777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209159 q = 1) (hb : d244767 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209159, d244767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79562 q ha hb
    | true =>
      simp only [d209159, d244767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209160 q = 1) (hb : d244768 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209160, d244768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209160, d244768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209164 q = 1) (hb : d244772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209164, d244772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79563 q ha hb
    | true =>
      simp only [d209164, d244772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209165 q = 1) (hb : d244773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209165, d244773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209165, d244773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209166 q = 1) (hb : d244774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209166, d244774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209166, d244774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209167 q = 1) (hb : d244775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209167, d244775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209167, d244775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209168 q = 1) (hb : d244776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209168, d244776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209168, d244776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209169 q = 1) (hb : d244777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209169, d244777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209169, d244777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79565 (p : Pattern) (ha : d209171 p = 1) (hb : d244779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209153 q = 1) (hb : d244761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
    | true =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79561 q ha hb
  have h2 (q : Pattern) (ha : d209154 q = 1) (hb : d244762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209155 q = 1) (hb : d244763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209161 q = 1) (hb : d244769 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209161, d244769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209161, d244769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209170 q = 1) (hb : d244778 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209170, d244778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209170, d244778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209171 q = 1) (hb : d244779 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209171, d244779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209171, d244779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79566 (p : Pattern) (ha : d209177 p = 1) (hb : d244785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209164 q = 1) (hb : d244772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209164, d244772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79563 q ha hb
    | true =>
      simp only [d209164, d244772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209165 q = 1) (hb : d244773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209165, d244773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209165, d244773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209172 q = 1) (hb : d244780 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209172, d244780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79565 q ha hb
    | true =>
      simp only [d209172, d244780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209173 q = 1) (hb : d244781 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209173, d244781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209173, d244781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209174 q = 1) (hb : d244782 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209174, d244782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209174, d244782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209175 q = 1) (hb : d244783 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209175, d244783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209175, d244783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209176 q = 1) (hb : d244784 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209176, d244784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209176, d244784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209177 q = 1) (hb : d244785 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209177, d244785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209177, d244785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79567 (p : Pattern) (ha : d74406 p = 1) (hb : d244794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74400 q = 1) (hb : d244788 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74400, d244788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74400, d244788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79541 q ha hb
  have h2 (q : Pattern) (ha : d74356 q = 1) (hb : d244672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79541 q ha hb
    | true =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74401 q = 1) (hb : d244789 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74401, d244789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74401, d244789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74357 q = 1) (hb : d244673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74402 q = 1) (hb : d244790 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74402, d244790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74402, d244790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74403 q = 1) (hb : d244791 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74403, d244791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74403, d244791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d74404 q = 1) (hb : d244792 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74404, d244792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74404, d244792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d74406 q = 1) (hb : d244794 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74406, d244794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74406, d244794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79568 (p : Pattern) (ha : d209185 p = 1) (hb : d244793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32496 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32496, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
  have h2 (q : Pattern) (ha : d32172 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79519 q ha hb
    | true =>
      simp only [d32172, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32497 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32497, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32173 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32173, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32498 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32498, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32499 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32499, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209137 q = 1) (hb : d244745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
  have h8 (q : Pattern) (ha : d208963 q = 1) (hb : d244588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79521 q ha hb
    | true =>
      simp only [d208963, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209138 q = 1) (hb : d244746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209138, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208964 q = 1) (hb : d244589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208964, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209139 q = 1) (hb : d244747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209139, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209140 q = 1) (hb : d244748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209140, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209141 q = 1) (hb : d244749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209141, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209141, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74400 q = 1) (hb : d244788 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74400, d244788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74400, d244788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79541 q ha hb
  have h15 (q : Pattern) (ha : d74356 q = 1) (hb : d244672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79541 q ha hb
    | true =>
      simp only [d74356, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74401 q = 1) (hb : d244789 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74401, d244789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74401, d244789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74357 q = 1) (hb : d244673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74357, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74402 q = 1) (hb : d244790 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74402, d244790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74402, d244790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74403 q = 1) (hb : d244791 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74403, d244791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74403, d244791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74404 q = 1) (hb : d244792 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74404, d244792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74404, d244792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209185 q = 1) (hb : d244793 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209185, d244793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209185, d244793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79569 (p : Pattern) (ha : d209191 p = 1) (hb : d244800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209148 q = 1) (hb : d244756 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209148, d244756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79559 q ha hb
    | true =>
      simp only [d209148, d244756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
  have h2 (q : Pattern) (ha : d209149 q = 1) (hb : d244757 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209149, d244757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209149, d244757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209150 q = 1) (hb : d244758 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209150, d244758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209150, d244758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209153 q = 1) (hb : d244761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79560 q ha hb
    | true =>
      simp only [d209153, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79561 q ha hb
  have h5 (q : Pattern) (ha : d209154 q = 1) (hb : d244762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209155 q = 1) (hb : d244763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209156 q = 1) (hb : d244764 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209156, d244764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209156, d244764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209186 q = 1) (hb : d244795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209186, d244795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79568 q ha hb
    | true =>
      simp only [d209186, d244795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79567 q ha hb
  have h9 (q : Pattern) (ha : d209187 q = 1) (hb : d244796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209187, d244796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209187, d244796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209188 q = 1) (hb : d244797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209188, d244797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209188, d244797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209189 q = 1) (hb : d244798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209189, d244798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209189, d244798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209190 q = 1) (hb : d244799 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209190, d244799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209190, d244799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209191 q = 1) (hb : d244800 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209191, d244800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209191, d244800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79570 (p : Pattern) (ha : d209197 p = 1) (hb : d244806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209192 q = 1) (hb : d244801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209192, d244801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79569 q ha hb
    | true =>
      simp only [d209192, d244801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209193 q = 1) (hb : d244802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209193, d244802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209193, d244802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209194 q = 1) (hb : d244803 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209194, d244803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209194, d244803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209195 q = 1) (hb : d244804 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209195, d244804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209195, d244804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209196 q = 1) (hb : d244805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209196, d244805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209196, d244805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209197 q = 1) (hb : d244806 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209197, d244806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209197, d244806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79571 (p : Pattern) (ha : d209203 p = 1) (hb : d244812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209178 q = 1) (hb : d244786 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209178, d244786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79564 q ha hb
    | true =>
      simp only [d209178, d244786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79566 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d244787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d244787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209184, d244787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209198 q = 1) (hb : d244807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209198, d244807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79570 q ha hb
    | true =>
      simp only [d209198, d244807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209199 q = 1) (hb : d244808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209199, d244808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209199, d244808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209200 q = 1) (hb : d244809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d244809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d244809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209201 q = 1) (hb : d244810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d244810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d244810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209202 q = 1) (hb : d244811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d244811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d244811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209203 q = 1) (hb : d244812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d244812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d244812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79572 (p : Pattern) (ha : d209182 p = 1) (hb : d244817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209172 q = 1) (hb : d244780 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209172, d244780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79565 q ha hb
    | true =>
      simp only [d209172, d244780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209173 q = 1) (hb : d244781 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209173, d244781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209173, d244781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209179 q = 1) (hb : d244814 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209179, d244814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209179, d244814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209180 q = 1) (hb : d244815 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209180, d244815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209180, d244815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209181 q = 1) (hb : d244816 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209181, d244816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209181, d244816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209182 q = 1) (hb : d244817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209182, d244817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209182, d244817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79573 (p : Pattern) (ha : d209210 p = 1) (hb : d244823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209205 q = 1) (hb : d244818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209205, d244818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79572 q ha hb
    | true =>
      simp only [d209205, d244818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209206 q = 1) (hb : d244819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209206, d244819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209206, d244819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209207 q = 1) (hb : d244820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209207, d244820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209207, d244820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209208 q = 1) (hb : d244821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209208, d244821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209208, d244821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209209 q = 1) (hb : d244822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209209, d244822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209209, d244822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209210 q = 1) (hb : d244823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209210, d244823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209210, d244823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79574 (p : Pattern) (ha : d209216 p = 1) (hb : d244829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209002 q = 1) (hb : d244627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209002, d244627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209002, d244627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79529 q ha hb
  have h2 (q : Pattern) (ha : d209003 q = 1) (hb : d244628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209003, d244628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209003, d244628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209012 q = 1) (hb : d244637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209012, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79529 q ha hb
    | true =>
      simp only [d209012, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79532 q ha hb
  have h4 (q : Pattern) (ha : d209013 q = 1) (hb : d244638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209013, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209013, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209014 q = 1) (hb : d244639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209014, d244639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209014, d244639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209095 q = 1) (hb : d244718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209095, d244718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79546 q ha hb
    | true =>
      simp only [d209095, d244718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79553 q ha hb
  have h7 (q : Pattern) (ha : d209108 q = 1) (hb : d244731 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209108, d244731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79554 q ha hb
    | true =>
      simp only [d209108, d244731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79555 q ha hb
  have h8 (q : Pattern) (ha : d209109 q = 1) (hb : d244732 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209109, d244732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209109, d244732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209110 q = 1) (hb : d244733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d244733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209110, d244733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209111 q = 1) (hb : d244734 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d244734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209111, d244734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209115 q = 1) (hb : d244738 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d244738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209115, d244738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79556 q ha hb
  have h12 (q : Pattern) (ha : d209117 q = 1) (hb : d244740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209117, d244740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209117, d244740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79557 q ha hb
  have h13 (q : Pattern) (ha : d209118 q = 1) (hb : d244741 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d244741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209118, d244741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209119 q = 1) (hb : d244742 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d244742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209119, d244742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209120 q = 1) (hb : d244743 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d244743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209120, d244743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209121 q = 1) (hb : d244744 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d244744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209121, d244744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209204 q = 1) (hb : d244813 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d244813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209204, d244813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79571 q ha hb
  have h18 (q : Pattern) (ha : d209211 q = 1) (hb : d244824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209211, d244824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209211, d244824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79573 q ha hb
  have h19 (q : Pattern) (ha : d209212 q = 1) (hb : d244825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d244825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209212, d244825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209213 q = 1) (hb : d244826 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d244826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209213, d244826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209214 q = 1) (hb : d244827 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d244827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209214, d244827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209215 q = 1) (hb : d244828 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d244828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209215, d244828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209216 q = 1) (hb : d244829 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d244829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209216, d244829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro79575 (p : Pattern) (ha : d209222 p = 1) (hb : d244835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d244830 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d244830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d244830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79574 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d244831 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d244831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d244831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d244832 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d244832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d244832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d244833 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d244833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d244833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d244834 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d244834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d244834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d244835 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d244835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d244835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79576 (p : Pattern) (ha : d32693 p = 1) (hb : d209229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32688 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32688, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75082 q ha hb
    | true =>
      simp only [d32688, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32689 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32689, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32689, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32690 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32690, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32690, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32691 q = 1) (hb : d209227 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32691, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32691, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32692 q = 1) (hb : d209228 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32692, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32692, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d32693 q = 1) (hb : d209229 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32693, d209229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32693, d209229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79577 (p : Pattern) (ha : d32707 p = 1) (hb : d209236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32688 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32688, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75082 q ha hb
    | true =>
      simp only [d32688, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32689 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32689, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32689, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32690 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32690, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32690, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32691 q = 1) (hb : d209227 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32691, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32691, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32692 q = 1) (hb : d209228 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32692, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32692, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d32699 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75082 q ha hb
    | true =>
      simp only [d32699, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75083 q ha hb
  have h10 (q : Pattern) (ha : d10055 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10055, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75081 q ha hb
  have h11 (q : Pattern) (ha : d32700 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32700, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d32702 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32702, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76359 q ha hb
    | true =>
      simp only [d32702, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d32703 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32703, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32703, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32704 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32704, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32704, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32705 q = 1) (hb : d209234 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32705, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32705, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h18 (q : Pattern) (ha : d32706 q = 1) (hb : d209235 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32706, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32706, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d32707 q = 1) (hb : d209236 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32707, d209236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32707, d209236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79578 (p : Pattern) (ha : d209244 p = 1) (hb : d244840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d32699 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75082 q ha hb
    | true =>
      simp only [d32699, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75083 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75081 q ha hb
  have h3 (q : Pattern) (ha : d32700 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32700, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32702 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32702, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76359 q ha hb
    | true =>
      simp only [d32702, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32703 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32703, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32703, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32704 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32704, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32704, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32705 q = 1) (hb : d209234 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32705, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32705, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d32706 q = 1) (hb : d209235 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32706, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32706, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h12 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h13 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d2060 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24705 q = 1) (hb : d209242 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24705, d209242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24705, d209242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d24706 q = 1) (hb : d209243 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24706, d209243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d24706, d209243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d209244 q = 1) (hb : d244840 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d209244, d244840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209244, d244840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro79579 (p : Pattern) (ha : d209250 p = 1) (hb : d244846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32694 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79576 q ha hb
    | true =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32695 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32696 q = 1) (hb : d209232 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32696, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32696, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32697 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32697, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32697, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32710 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32711 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32712 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32712, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32712, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209247 q = 1) (hb : d244843 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209248 q = 1) (hb : d244844 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d209249 q = 1) (hb : d244845 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209249, d244845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d209249, d244845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209250 q = 1) (hb : d244846 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209250, d244846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209250, d244846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79580 (p : Pattern) (ha : d209252 p = 1) (hb : d244848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32710 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32711 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209247 q = 1) (hb : d244843 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209248 q = 1) (hb : d244844 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209249 q = 1) (hb : d244845 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209249, d244845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209249, d244845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209251 q = 1) (hb : d244847 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209251, d244847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209251, d244847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209252 q = 1) (hb : d244848 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209252, d244848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209252, d244848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79581 (p : Pattern) (ha : d209256 p = 1) (hb : d244852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209247 q = 1) (hb : d244843 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209248 q = 1) (hb : d244844 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209251 q = 1) (hb : d244847 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209251, d244847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209251, d244847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2082 q = 1) (hb : d53361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2083 q = 1) (hb : d53362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2084 q = 1) (hb : d53363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d209256 q = 1) (hb : d244852 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209256, d244852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209256, d244852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro79582 (p : Pattern) (ha : d209263 p = 1) (hb : d244859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209253 q = 1) (hb : d244849 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209253, d244849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79579 q ha hb
    | true =>
      simp only [d209253, d244849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
  have h2 (q : Pattern) (ha : d209254 q = 1) (hb : d244850 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209254, d244850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209254, d244850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209255 q = 1) (hb : d244851 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209255, d244851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209255, d244851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209257 q = 1) (hb : d244853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
    | true =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79581 q ha hb
  have h5 (q : Pattern) (ha : d209258 q = 1) (hb : d244854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209259 q = 1) (hb : d244855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209260 q = 1) (hb : d244856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d244856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209260, d244856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209261 q = 1) (hb : d244857 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209261, d244857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209261, d244857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209262 q = 1) (hb : d244858 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209262, d244858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209262, d244858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209263 q = 1) (hb : d244859 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209263, d244859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209263, d244859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro79583 (p : Pattern) (ha : d209267 p = 1) (hb : d244863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209257 q = 1) (hb : d244853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
    | true =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79581 q ha hb
  have h2 (q : Pattern) (ha : d209258 q = 1) (hb : d244854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209259 q = 1) (hb : d244855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209261 q = 1) (hb : d244857 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209261, d244857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209261, d244857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209266 q = 1) (hb : d244862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209266, d244862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209266, d244862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209267 q = 1) (hb : d244863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209267, d244863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209267, d244863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79584 (p : Pattern) (ha : d209273 p = 1) (hb : d244869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d244866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d244867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209272 q = 1) (hb : d244868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209272, d244868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209272, d244868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209273 q = 1) (hb : d244869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209273, d244869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209273, d244869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79585 (p : Pattern) (ha : d209277 p = 1) (hb : d244873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d244870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d244871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209276 q = 1) (hb : d244872 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209276, d244872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209276, d244872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209277 q = 1) (hb : d244873 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209277, d244873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209277, d244873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79586 (p : Pattern) (ha : d209283 p = 1) (hb : d244879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
    | true =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209283 q = 1) (hb : d244879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209283, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209283, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79587 (p : Pattern) (ha : d209286 p = 1) (hb : d244882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d244866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d244867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209272 q = 1) (hb : d244868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209272, d244868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209272, d244868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209286 q = 1) (hb : d244882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209286, d244882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209286, d244882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79588 (p : Pattern) (ha : d209287 p = 1) (hb : d244883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d244870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d244871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209276 q = 1) (hb : d244872 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209276, d244872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209276, d244872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209287 q = 1) (hb : d244883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209287, d244883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209287, d244883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79589 (p : Pattern) (ha : d209293 p = 1) (hb : d244889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
    | true =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209288 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79587 q ha hb
    | true =>
      simp only [d209288, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79588 q ha hb
  have h7 (q : Pattern) (ha : d209289 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209289, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209289, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209290 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209290, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209290, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209291 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209291, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209291, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209292 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209292, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209292, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209293 q = 1) (hb : d244889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209293, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209293, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79590 (p : Pattern) (ha : d209298 p = 1) (hb : d244894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d244866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d244867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209297 q = 1) (hb : d244893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209297, d244893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209297, d244893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209298 q = 1) (hb : d244894 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209298, d244894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209298, d244894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79591 (p : Pattern) (ha : d209300 p = 1) (hb : d244896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d244870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d244871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209299 q = 1) (hb : d244895 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209299, d244895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209299, d244895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209300 q = 1) (hb : d244896 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209300, d244896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209300, d244896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79592 (p : Pattern) (ha : d209307 p = 1) (hb : d244903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d244866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209305 q = 1) (hb : d244901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209305, d244901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209305, d244901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209306 q = 1) (hb : d244902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209306, d244902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209306, d244902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209307 q = 1) (hb : d244903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209307, d244903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209307, d244903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79593 (p : Pattern) (ha : d209310 p = 1) (hb : d244906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d244870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209308 q = 1) (hb : d244904 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209308, d244904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209308, d244904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209309 q = 1) (hb : d244905 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209309, d244905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209309, d244905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209310 q = 1) (hb : d244906 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209310, d244906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209310, d244906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79594 (p : Pattern) (ha : d32803 p = 1) (hb : d209315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32694 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79576 q ha hb
    | true =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32695 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d32696 q = 1) (hb : d209232 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32696, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32696, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32697 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32697, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32697, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32802 q = 1) (hb : d209314 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32802, d209314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32802, d209314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d32710 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32711 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d32712 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32712, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32712, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32803 q = 1) (hb : d209315 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32803, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32803, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79595 (p : Pattern) (ha : d209321 p = 1) (hb : d244915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209316 q = 1) (hb : d244910 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209316, d244910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79594 q hb ha
    | true =>
      simp only [d209316, d244910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79579 q ha hb
  have h2 (q : Pattern) (ha : d209317 q = 1) (hb : d244911 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209317, d244911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209317, d244911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209318 q = 1) (hb : d244912 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209318, d244912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209318, d244912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209253 q = 1) (hb : d244849 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209253, d244849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79579 q ha hb
    | true =>
      simp only [d209253, d244849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
  have h5 (q : Pattern) (ha : d209254 q = 1) (hb : d244850 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209254, d244850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209254, d244850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209255 q = 1) (hb : d244851 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209255, d244851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209255, d244851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209319 q = 1) (hb : d244913 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209319, d244913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209319, d244913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209257 q = 1) (hb : d244853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
    | true =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79581 q ha hb
  have h9 (q : Pattern) (ha : d209258 q = 1) (hb : d244854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209259 q = 1) (hb : d244855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209260 q = 1) (hb : d244856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d244856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209260, d244856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209320 q = 1) (hb : d244914 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209320, d244914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209320, d244914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209321 q = 1) (hb : d244915 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209321, d244915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209321, d244915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79596 (p : Pattern) (ha : d209327 p = 1) (hb : d244921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209322 q = 1) (hb : d244916 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209322, d244916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79595 q ha hb
    | true =>
      simp only [d209322, d244916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209323 q = 1) (hb : d244917 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209323, d244917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209323, d244917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209324 q = 1) (hb : d244918 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209324, d244918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209324, d244918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209325 q = 1) (hb : d244919 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209325, d244919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209325, d244919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209326 q = 1) (hb : d244920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209326, d244920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209326, d244920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209327 q = 1) (hb : d244921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209327, d244921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209327, d244921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79597 (p : Pattern) (ha : d74446 p = 1) (hb : d244924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d32699 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75082 q ha hb
    | true =>
      simp only [d32699, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75083 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75081 q ha hb
  have h3 (q : Pattern) (ha : d32700 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32700, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32902 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32902, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32902, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d32903 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32903, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32903, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32904 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32904, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32904, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h8 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5718 q = 1) (hb : d74444 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5718, d74444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5718, d74444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d5719 q = 1) (hb : d74445 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5719, d74445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5719, d74445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d74446 q = 1) (hb : d244924 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d74446, d244924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74446, d244924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro79598 (p : Pattern) (ha : d74453 p = 1) (hb : d244931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74447 q = 1) (hb : d244925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79597 q ha hb
    | true =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74448 q = 1) (hb : d244926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74449 q = 1) (hb : d244927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74449, d244927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74449, d244927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74450 q = 1) (hb : d244928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74450, d244928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74450, d244928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74451 q = 1) (hb : d244929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74451, d244929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74451, d244929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74453 q = 1) (hb : d244931 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74453, d244931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74453, d244931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79599 (p : Pattern) (ha : d209330 p = 1) (hb : d244930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32710 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32710, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32711 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32711, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209247 q = 1) (hb : d244843 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209247, d244843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209248 q = 1) (hb : d244844 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209248, d244844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209249 q = 1) (hb : d244845 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209249, d244845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209249, d244845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74447 q = 1) (hb : d244925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79597 q ha hb
    | true =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74448 q = 1) (hb : d244926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74449 q = 1) (hb : d244927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74449, d244927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74449, d244927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74450 q = 1) (hb : d244928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74450, d244928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74450, d244928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74451 q = 1) (hb : d244929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74451, d244929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74451, d244929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209330 q = 1) (hb : d244930 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209330, d244930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209330, d244930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79600 (p : Pattern) (ha : d209336 p = 1) (hb : d244937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209253 q = 1) (hb : d244849 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209253, d244849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79579 q ha hb
    | true =>
      simp only [d209253, d244849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
  have h2 (q : Pattern) (ha : d209254 q = 1) (hb : d244850 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209254, d244850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209254, d244850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209255 q = 1) (hb : d244851 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209255, d244851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209255, d244851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209257 q = 1) (hb : d244853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79580 q ha hb
    | true =>
      simp only [d209257, d244853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79581 q ha hb
  have h5 (q : Pattern) (ha : d209258 q = 1) (hb : d244854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d244854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209259 q = 1) (hb : d244855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d244855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209260 q = 1) (hb : d244856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d244856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209260, d244856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209331 q = 1) (hb : d244932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209331, d244932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79599 q ha hb
    | true =>
      simp only [d209331, d244932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79598 q ha hb
  have h9 (q : Pattern) (ha : d209332 q = 1) (hb : d244933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209332, d244933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209332, d244933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209333 q = 1) (hb : d244934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209333, d244934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209333, d244934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209334 q = 1) (hb : d244935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209334, d244935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209334, d244935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209335 q = 1) (hb : d244936 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209335, d244936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209335, d244936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209336 q = 1) (hb : d244937 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209336, d244937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209336, d244937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79601 (p : Pattern) (ha : d209342 p = 1) (hb : d244943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209337 q = 1) (hb : d244938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209337, d244938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79600 q ha hb
    | true =>
      simp only [d209337, d244938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209338 q = 1) (hb : d244939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209338, d244939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209338, d244939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209339 q = 1) (hb : d244940 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209339, d244940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209339, d244940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209340 q = 1) (hb : d244941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209340, d244941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209340, d244941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209341 q = 1) (hb : d244942 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209341, d244942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209341, d244942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209342 q = 1) (hb : d244943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209342, d244943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209342, d244943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79602 (p : Pattern) (ha : d209348 p = 1) (hb : d244949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209301 q = 1) (hb : d244897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209301, d244897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79590 q ha hb
    | true =>
      simp only [d209301, d244897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79591 q ha hb
  have h2 (q : Pattern) (ha : d209302 q = 1) (hb : d244898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209302, d244898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209302, d244898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209303 q = 1) (hb : d244899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209303, d244899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209303, d244899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209304 q = 1) (hb : d244900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209304, d244900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209304, d244900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209311 q = 1) (hb : d244907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209311, d244907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79592 q ha hb
    | true =>
      simp only [d209311, d244907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79593 q ha hb
  have h6 (q : Pattern) (ha : d209312 q = 1) (hb : d244908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209312, d244908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209312, d244908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209313 q = 1) (hb : d244909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209313, d244909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209313, d244909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209328 q = 1) (hb : d244922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209328, d244922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79596 q ha hb
    | true =>
      simp only [d209328, d244922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d244923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d244923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209329, d244923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209343 q = 1) (hb : d244944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209343, d244944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79601 q ha hb
    | true =>
      simp only [d209343, d244944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209344 q = 1) (hb : d244945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209344, d244945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209344, d244945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d244946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d244946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d244946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d244947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d244947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209346, d244947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d244948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d244948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209347, d244948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209348 q = 1) (hb : d244949 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d244949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d244949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79603 (p : Pattern) (ha : d209349 p = 1) (hb : d244950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d244866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d244867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d244867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209297 q = 1) (hb : d244893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209297, d244893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209297, d244893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209349 q = 1) (hb : d244950 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209349, d244950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209349, d244950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79604 (p : Pattern) (ha : d209350 p = 1) (hb : d244951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d244870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d244871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d244871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209299 q = 1) (hb : d244895 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209299, d244895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209299, d244895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209350 q = 1) (hb : d244951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209350, d244951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209350, d244951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79605 (p : Pattern) (ha : d209355 p = 1) (hb : d244956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d244866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d244866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209305 q = 1) (hb : d244901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209305, d244901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209305, d244901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209306 q = 1) (hb : d244902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209306, d244902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209306, d244902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209355 q = 1) (hb : d244956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209355, d244956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209355, d244956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79606 (p : Pattern) (ha : d209356 p = 1) (hb : d244957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d244864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79583 q ha hb
    | true =>
      simp only [d209268, d244864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d244865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d244865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d244870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d244870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209308 q = 1) (hb : d244904 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209308, d244904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209308, d244904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209309 q = 1) (hb : d244905 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209309, d244905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209309, d244905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209356 q = 1) (hb : d244957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209356, d244957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209356, d244957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79607 (p : Pattern) (ha : d209360 p = 1) (hb : d244961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209322 q = 1) (hb : d244916 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209322, d244916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79595 q ha hb
    | true =>
      simp only [d209322, d244916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209323 q = 1) (hb : d244917 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209323, d244917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209323, d244917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209264 q = 1) (hb : d244860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79582 q ha hb
    | true =>
      simp only [d209264, d244860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209265 q = 1) (hb : d244861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d244861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209324 q = 1) (hb : d244918 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209324, d244918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209324, d244918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209325 q = 1) (hb : d244919 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209325, d244919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209325, d244919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209326 q = 1) (hb : d244920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209326, d244920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209326, d244920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209360 q = 1) (hb : d244961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209360, d244961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209360, d244961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79608 (p : Pattern) (ha : d209363 p = 1) (hb : d244964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209337 q = 1) (hb : d244938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209337, d244938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79600 q ha hb
    | true =>
      simp only [d209337, d244938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209338 q = 1) (hb : d244939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209338, d244939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209338, d244939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209339 q = 1) (hb : d244940 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209339, d244940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209339, d244940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209340 q = 1) (hb : d244941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209340, d244941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209340, d244941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209341 q = 1) (hb : d244942 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209341, d244942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209341, d244942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209363 q = 1) (hb : d244964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209363, d244964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209363, d244964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79609 (p : Pattern) (ha : d209369 p = 1) (hb : d244970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209301 q = 1) (hb : d244897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209301, d244897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79590 q ha hb
    | true =>
      simp only [d209301, d244897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79591 q ha hb
  have h2 (q : Pattern) (ha : d209302 q = 1) (hb : d244898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209302, d244898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209302, d244898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209303 q = 1) (hb : d244899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209303, d244899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209303, d244899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209304 q = 1) (hb : d244900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209304, d244900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209304, d244900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209311 q = 1) (hb : d244907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209311, d244907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79592 q ha hb
    | true =>
      simp only [d209311, d244907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79593 q ha hb
  have h6 (q : Pattern) (ha : d209312 q = 1) (hb : d244908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209312, d244908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209312, d244908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209313 q = 1) (hb : d244909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209313, d244909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209313, d244909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209328 q = 1) (hb : d244922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209328, d244922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79596 q ha hb
    | true =>
      simp only [d209328, d244922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d244923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d244923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209329, d244923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209343 q = 1) (hb : d244944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209343, d244944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79601 q ha hb
    | true =>
      simp only [d209343, d244944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209344 q = 1) (hb : d244945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209344, d244945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209344, d244945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d244946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d244946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d244946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d244947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d244947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209346, d244947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d244948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d244948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209347, d244948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209351 q = 1) (hb : d244952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209351, d244952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79603 q ha hb
    | true =>
      simp only [d209351, d244952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79604 q ha hb
  have h17 (q : Pattern) (ha : d209352 q = 1) (hb : d244953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209352, d244953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209352, d244953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209353 q = 1) (hb : d244954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209353, d244954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209353, d244954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d209354 q = 1) (hb : d244955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209354, d244955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209354, d244955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209357 q = 1) (hb : d244958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209357, d244958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79605 q ha hb
    | true =>
      simp only [d209357, d244958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79606 q ha hb
  have h21 (q : Pattern) (ha : d209358 q = 1) (hb : d244959 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209358, d244959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209358, d244959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d209359 q = 1) (hb : d244960 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209359, d244960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209359, d244960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209361 q = 1) (hb : d244962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209361, d244962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79607 q ha hb
    | true =>
      simp only [d209361, d244962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79587 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209362 q = 1) (hb : d244963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d244963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d209362, d244963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d209364 q = 1) (hb : d244965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209364, d244965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79608 q ha hb
    | true =>
      simp only [d209364, d244965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d209365 q = 1) (hb : d244966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209365, d244966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d209365, d244966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d209366 q = 1) (hb : d244967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d244967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209366, d244967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d209367 q = 1) (hb : d244968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d244968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d209367, d244968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209368 q = 1) (hb : d244969 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d244969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209368, d244969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209369 q = 1) (hb : d244970 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d244970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209369, d244970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro79610 (p : Pattern) (ha : d209376 p = 1) (hb : d244977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
    | true =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209371 q = 1) (hb : d244972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209371, d244972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
    | true =>
      simp only [d209371, d244972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209372 q = 1) (hb : d244973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209372, d244973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209372, d244973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209373 q = 1) (hb : d244974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209373, d244974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209373, d244974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209374 q = 1) (hb : d244975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209374, d244975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209374, d244975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209375 q = 1) (hb : d244976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209375, d244976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209375, d244976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209376 q = 1) (hb : d244977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209376, d244977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209376, d244977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79611 (p : Pattern) (ha : d209382 p = 1) (hb : d244983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209371 q = 1) (hb : d244972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209371, d244972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
    | true =>
      simp only [d209371, d244972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209372 q = 1) (hb : d244973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209372, d244973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209372, d244973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209373 q = 1) (hb : d244974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209373, d244974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209373, d244974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209374 q = 1) (hb : d244975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209374, d244975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209374, d244975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209375 q = 1) (hb : d244976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209375, d244976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209375, d244976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209377 q = 1) (hb : d244978 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209377, d244978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79588 q ha hb
    | true =>
      simp only [d209377, d244978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209378 q = 1) (hb : d244979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209378, d244979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209378, d244979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209379 q = 1) (hb : d244980 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209379, d244980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209379, d244980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209380 q = 1) (hb : d244981 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209380, d244981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209380, d244981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209381 q = 1) (hb : d244982 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209381, d244982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209381, d244982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209382 q = 1) (hb : d244983 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209382, d244983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209382, d244983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79612 (p : Pattern) (ha : d209389 p = 1) (hb : d244990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209361 q = 1) (hb : d244962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209361, d244962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79607 q ha hb
    | true =>
      simp only [d209361, d244962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79587 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d244963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d244963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209362, d244963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209364 q = 1) (hb : d244965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209364, d244965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79608 q ha hb
    | true =>
      simp only [d209364, d244965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209365 q = 1) (hb : d244966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209365, d244966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209365, d244966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209366 q = 1) (hb : d244967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d244967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d244967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209387 q = 1) (hb : d244988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d244988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d244988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209388 q = 1) (hb : d244989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d244989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d244989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209389 q = 1) (hb : d244990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d244990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d244990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79613 (p : Pattern) (ha : d209391 p = 1) (hb : d244992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209377 q = 1) (hb : d244978 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209377, d244978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79588 q ha hb
    | true =>
      simp only [d209377, d244978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209378 q = 1) (hb : d244979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209378, d244979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209378, d244979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209379 q = 1) (hb : d244980 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209379, d244980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209379, d244980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209380 q = 1) (hb : d244981 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209380, d244981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209380, d244981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209381 q = 1) (hb : d244982 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209381, d244982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209381, d244982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209391 q = 1) (hb : d244992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209391, d244992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209391, d244992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79614 (p : Pattern) (ha : d33001 p = 1) (hb : d209407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32991 q = 1) (hb : d209397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32991, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32991, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79576 q ha hb
  have h3 (q : Pattern) (ha : d32694 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79576 q ha hb
    | true =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d32992 q = 1) (hb : d209398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32992, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32992, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32695 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32993 q = 1) (hb : d209399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32993, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32993, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32994 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32994, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32994, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d32995 q = 1) (hb : d209401 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32995, d209401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32995, d209401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32996 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
  have h10 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d32997 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d32998 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32999 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d33000 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33000, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33000, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33001 q = 1) (hb : d209407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33001, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33001, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79615 (p : Pattern) (ha : d209413 p = 1) (hb : d245003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32991 q = 1) (hb : d209397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32991, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32991, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79576 q ha hb
  have h2 (q : Pattern) (ha : d32694 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79576 q ha hb
    | true =>
      simp only [d32694, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32992 q = 1) (hb : d209398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32992, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32992, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32695 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32695, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32993 q = 1) (hb : d209399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32993, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32993, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32994 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32994, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32994, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32996 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
  have h8 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32997 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32998 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32999 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33000 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33000, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33000, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209408 q = 1) (hb : d244998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
  have h15 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209409 q = 1) (hb : d244999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d209410 q = 1) (hb : d245000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d209411 q = 1) (hb : d245001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d209412 q = 1) (hb : d245002 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209412, d245002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d209412, d245002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d209413 q = 1) (hb : d245003 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209413, d245003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d209413, d245003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79616 (p : Pattern) (ha : d209418 p = 1) (hb : d245008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32996 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
  have h2 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32997 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32998 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32999 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209408 q = 1) (hb : d244998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
  have h8 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209409 q = 1) (hb : d244999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209410 q = 1) (hb : d245000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209411 q = 1) (hb : d245001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209412 q = 1) (hb : d245002 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209412, d245002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209412, d245002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209417 q = 1) (hb : d245007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209417, d245007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209417, d245007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209418 q = 1) (hb : d245008 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209418, d245008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209418, d245008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79617 (p : Pattern) (ha : d209423 p = 1) (hb : d245013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209408 q = 1) (hb : d244998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
  have h2 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209409 q = 1) (hb : d244999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209410 q = 1) (hb : d245000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209411 q = 1) (hb : d245001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209417 q = 1) (hb : d245007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209417, d245007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209417, d245007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d2361 q = 1) (hb : d53526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
  have h9 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2362 q = 1) (hb : d53527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2363 q = 1) (hb : d53528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2364 q = 1) (hb : d53529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2365 q = 1) (hb : d53530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d209423 q = 1) (hb : d245013 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209423, d245013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209423, d245013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro79618 (p : Pattern) (ha : d209429 p = 1) (hb : d245019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209414 q = 1) (hb : d245004 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209414, d245004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79614 q hb ha
    | true =>
      simp only [d209414, d245004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79615 q ha hb
  have h2 (q : Pattern) (ha : d209415 q = 1) (hb : d245005 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209415, d245005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209415, d245005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209416 q = 1) (hb : d245006 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209416, d245006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209416, d245006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209419 q = 1) (hb : d245009 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209419, d245009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79615 q ha hb
    | true =>
      simp only [d209419, d245009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
  have h5 (q : Pattern) (ha : d209420 q = 1) (hb : d245010 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209420, d245010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209420, d245010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209421 q = 1) (hb : d245011 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209421, d245011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209421, d245011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209422 q = 1) (hb : d245012 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209422, d245012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209422, d245012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209424 q = 1) (hb : d245014 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
    | true =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79617 q ha hb
  have h9 (q : Pattern) (ha : d209425 q = 1) (hb : d245015 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209426 q = 1) (hb : d245016 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209427 q = 1) (hb : d245017 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d245017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209427, d245017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209428 q = 1) (hb : d245018 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209428, d245018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209428, d245018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209429 q = 1) (hb : d245019 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209429, d245019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209429, d245019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79619 (p : Pattern) (ha : d209434 p = 1) (hb : d245024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209419 q = 1) (hb : d245009 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209419, d245009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79615 q ha hb
    | true =>
      simp only [d209419, d245009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
  have h2 (q : Pattern) (ha : d209420 q = 1) (hb : d245010 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209420, d245010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209420, d245010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209421 q = 1) (hb : d245011 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209421, d245011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209421, d245011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209424 q = 1) (hb : d245014 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
    | true =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79617 q ha hb
  have h5 (q : Pattern) (ha : d209425 q = 1) (hb : d245015 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209426 q = 1) (hb : d245016 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209427 q = 1) (hb : d245017 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d245017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209427, d245017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209432 q = 1) (hb : d245022 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209432, d245022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209432, d245022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209433 q = 1) (hb : d245023 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209433, d245023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209433, d245023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209434 q = 1) (hb : d245024 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209434, d245024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209434, d245024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro79620 (p : Pattern) (ha : d209440 p = 1) (hb : d245030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209430 q = 1) (hb : d245020 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209430, d245020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79618 q ha hb
    | true =>
      simp only [d209430, d245020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209431 q = 1) (hb : d245021 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209431, d245021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209431, d245021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209435 q = 1) (hb : d245025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209435, d245025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79619 q ha hb
    | true =>
      simp only [d209435, d245025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209436 q = 1) (hb : d245026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209436, d245026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209436, d245026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209437 q = 1) (hb : d245027 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209437, d245027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209437, d245027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209438 q = 1) (hb : d245028 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209438, d245028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209438, d245028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209439 q = 1) (hb : d245029 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209439, d245029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209439, d245029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209440 q = 1) (hb : d245030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209440, d245030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209440, d245030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79621 (p : Pattern) (ha : d209442 p = 1) (hb : d245032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209424 q = 1) (hb : d245014 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
    | true =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79617 q ha hb
  have h2 (q : Pattern) (ha : d209425 q = 1) (hb : d245015 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209426 q = 1) (hb : d245016 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209432 q = 1) (hb : d245022 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209432, d245022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209432, d245022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209441 q = 1) (hb : d245031 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209441, d245031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209441, d245031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209442 q = 1) (hb : d245032 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209442, d245032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209442, d245032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79622 (p : Pattern) (ha : d209448 p = 1) (hb : d245038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209435 q = 1) (hb : d245025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209435, d245025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79619 q ha hb
    | true =>
      simp only [d209435, d245025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209436 q = 1) (hb : d245026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209436, d245026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209436, d245026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209443 q = 1) (hb : d245033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209443, d245033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79621 q ha hb
    | true =>
      simp only [d209443, d245033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209444 q = 1) (hb : d245034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209444, d245034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209444, d245034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209445 q = 1) (hb : d245035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209445, d245035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209445, d245035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209446 q = 1) (hb : d245036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209446, d245036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209446, d245036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209447 q = 1) (hb : d245037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209447, d245037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209447, d245037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209448 q = 1) (hb : d245038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209448, d245038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209448, d245038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79623 (p : Pattern) (ha : d74497 p = 1) (hb : d245047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74491 q = 1) (hb : d245041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74491, d245041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74491, d245041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79597 q ha hb
  have h2 (q : Pattern) (ha : d74447 q = 1) (hb : d244925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79597 q ha hb
    | true =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74492 q = 1) (hb : d245042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74492, d245042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74492, d245042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74448 q = 1) (hb : d244926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74493 q = 1) (hb : d245043 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74493, d245043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74493, d245043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74494 q = 1) (hb : d245044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74494, d245044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74494, d245044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d74495 q = 1) (hb : d245045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74495, d245045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74495, d245045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d74497 q = 1) (hb : d245047 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74497, d245047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74497, d245047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro79624 (p : Pattern) (ha : d209456 p = 1) (hb : d245046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32996 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32996, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
  have h2 (q : Pattern) (ha : d32708 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79577 q ha hb
    | true =>
      simp only [d32708, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32997 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32997, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32709 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32709, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32998 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32998, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32999 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32999, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209408 q = 1) (hb : d244998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d244998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
  have h8 (q : Pattern) (ha : d209245 q = 1) (hb : d244841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79578 q ha hb
    | true =>
      simp only [d209245, d244841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209409 q = 1) (hb : d244999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209409, d244999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209246 q = 1) (hb : d244842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209246, d244842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209410 q = 1) (hb : d245000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209410, d245000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209411 q = 1) (hb : d245001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209411, d245001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209412 q = 1) (hb : d245002 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209412, d245002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209412, d245002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74491 q = 1) (hb : d245041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74491, d245041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74491, d245041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79597 q ha hb
  have h15 (q : Pattern) (ha : d74447 q = 1) (hb : d244925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79597 q ha hb
    | true =>
      simp only [d74447, d244925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74492 q = 1) (hb : d245042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74492, d245042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74492, d245042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74448 q = 1) (hb : d244926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74448, d244926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74493 q = 1) (hb : d245043 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74493, d245043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74493, d245043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74494 q = 1) (hb : d245044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74494, d245044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74494, d245044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74495 q = 1) (hb : d245045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74495, d245045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74495, d245045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209456 q = 1) (hb : d245046 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209456, d245046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209456, d245046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79625 (p : Pattern) (ha : d209462 p = 1) (hb : d245053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209419 q = 1) (hb : d245009 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209419, d245009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79615 q ha hb
    | true =>
      simp only [d209419, d245009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
  have h2 (q : Pattern) (ha : d209420 q = 1) (hb : d245010 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209420, d245010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209420, d245010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209421 q = 1) (hb : d245011 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209421, d245011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209421, d245011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209424 q = 1) (hb : d245014 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79616 q ha hb
    | true =>
      simp only [d209424, d245014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79617 q ha hb
  have h5 (q : Pattern) (ha : d209425 q = 1) (hb : d245015 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d245015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209426 q = 1) (hb : d245016 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d245016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209427 q = 1) (hb : d245017 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d245017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209427, d245017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209457 q = 1) (hb : d245048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209457, d245048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79624 q ha hb
    | true =>
      simp only [d209457, d245048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79623 q ha hb
  have h9 (q : Pattern) (ha : d209458 q = 1) (hb : d245049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209458, d245049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209458, d245049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209459 q = 1) (hb : d245050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209459, d245050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209459, d245050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209460 q = 1) (hb : d245051 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209460, d245051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209460, d245051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209461 q = 1) (hb : d245052 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209461, d245052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209461, d245052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209462 q = 1) (hb : d245053 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209462, d245053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209462, d245053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro79626 (p : Pattern) (ha : d209468 p = 1) (hb : d245059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209463 q = 1) (hb : d245054 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209463, d245054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79625 q ha hb
    | true =>
      simp only [d209463, d245054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209464 q = 1) (hb : d245055 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209464, d245055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209464, d245055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209465 q = 1) (hb : d245056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209465, d245056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209465, d245056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209466 q = 1) (hb : d245057 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209466, d245057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209466, d245057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209467 q = 1) (hb : d245058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209467, d245058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209467, d245058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209468 q = 1) (hb : d245059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209468, d245059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209468, d245059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79627 (p : Pattern) (ha : d209474 p = 1) (hb : d245065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209449 q = 1) (hb : d245039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209449, d245039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79620 q ha hb
    | true =>
      simp only [d209449, d245039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d245040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d245040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209455, d245040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209469 q = 1) (hb : d245060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209469, d245060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79626 q ha hb
    | true =>
      simp only [d209469, d245060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209470 q = 1) (hb : d245061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209470, d245061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209470, d245061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209471 q = 1) (hb : d245062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d245062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d245062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209472 q = 1) (hb : d245063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d245063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d245063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209473 q = 1) (hb : d245064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d245064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d245064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209474 q = 1) (hb : d245065 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d245065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d245065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79628 (p : Pattern) (ha : d209453 p = 1) (hb : d245070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209443 q = 1) (hb : d245033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209443, d245033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79621 q ha hb
    | true =>
      simp only [d209443, d245033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209444 q = 1) (hb : d245034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209444, d245034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209444, d245034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209450 q = 1) (hb : d245067 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209450, d245067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209450, d245067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209451 q = 1) (hb : d245068 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209451, d245068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209451, d245068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209452 q = 1) (hb : d245069 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209452, d245069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209452, d245069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209453 q = 1) (hb : d245070 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209453, d245070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209453, d245070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79629 (p : Pattern) (ha : d209481 p = 1) (hb : d245076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209476 q = 1) (hb : d245071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209476, d245071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79628 q ha hb
    | true =>
      simp only [d209476, d245071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209477 q = 1) (hb : d245072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209477, d245072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209477, d245072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209478 q = 1) (hb : d245073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209478, d245073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209478, d245073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209479 q = 1) (hb : d245074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209479, d245074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209479, d245074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209480 q = 1) (hb : d245075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209480, d245075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209480, d245075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209481 q = 1) (hb : d245076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209481, d245076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209481, d245076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79630 (p : Pattern) (ha : d209487 p = 1) (hb : d245082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209284 q = 1) (hb : d244880 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209284, d244880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209284, d244880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79586 q ha hb
  have h2 (q : Pattern) (ha : d209285 q = 1) (hb : d244881 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209285, d244881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209285, d244881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209294 q = 1) (hb : d244890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209294, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79586 q ha hb
    | true =>
      simp only [d209294, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79589 q ha hb
  have h4 (q : Pattern) (ha : d209295 q = 1) (hb : d244891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209295, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209295, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209296 q = 1) (hb : d244892 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209296, d244892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209296, d244892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209370 q = 1) (hb : d244971 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d244971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79602 q ha hb
    | true =>
      simp only [d209370, d244971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79609 q ha hb
  have h7 (q : Pattern) (ha : d209383 q = 1) (hb : d244984 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209383, d244984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79610 q ha hb
    | true =>
      simp only [d209383, d244984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79611 q ha hb
  have h8 (q : Pattern) (ha : d209384 q = 1) (hb : d244985 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d244985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209384, d244985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209385 q = 1) (hb : d244986 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d244986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209385, d244986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209386 q = 1) (hb : d244987 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d244987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209386, d244987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209390 q = 1) (hb : d244991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d244991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209390, d244991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79612 q ha hb
  have h12 (q : Pattern) (ha : d209392 q = 1) (hb : d244993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209392, d244993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209392, d244993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79613 q ha hb
  have h13 (q : Pattern) (ha : d209393 q = 1) (hb : d244994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d244994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209393, d244994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209394 q = 1) (hb : d244995 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d244995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209394, d244995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209395 q = 1) (hb : d244996 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d244996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209395, d244996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209396 q = 1) (hb : d244997 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d244997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209396, d244997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209475 q = 1) (hb : d245066 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d245066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209475, d245066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79627 q ha hb
  have h18 (q : Pattern) (ha : d209482 q = 1) (hb : d245077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209482, d245077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209482, d245077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79629 q ha hb
  have h19 (q : Pattern) (ha : d209483 q = 1) (hb : d245078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d245078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209483, d245078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209484 q = 1) (hb : d245079 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d245079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209484, d245079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209485 q = 1) (hb : d245080 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d245080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209485, d245080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209486 q = 1) (hb : d245081 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d245081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209486, d245081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209487 q = 1) (hb : d245082 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d245082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209487, d245082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro79631 (p : Pattern) (ha : d209493 p = 1) (hb : d245088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d245083 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d245083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d245083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79630 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d245084 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d245084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d245084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d245085 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d245085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d245085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d245086 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d245086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d245086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d245087 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d245087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d245087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d245088 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d245088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d245088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79632 (p : Pattern) (ha : d209499 p = 1) (hb : d245094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d244110 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d244110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79374 q ha hb
    | true =>
      simp only [d208438, d244110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79414 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d244333 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d244333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d244333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79461 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d244334 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d244334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d244334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d244584 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d244584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d244584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79518 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d244585 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d244585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d244585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d244586 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d244586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d244586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d244836 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d244836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d244836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79575 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d244837 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d244837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d244837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d244838 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d244838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d244838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d244839 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d244839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d244839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d245089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d245089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d245089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79631 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d245090 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d245090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d245090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d245091 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d245091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d245091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d245092 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d245092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d245092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d245093 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d245093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d245093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d245094 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d245094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d245094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro79633 (p : Pattern) (ha : d209505 p = 1) (hb : d245100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d245095 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d245095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79632 q ha hb
    | true =>
      simp only [d209500, d245095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d245096 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d245096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d245096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d245097 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d245097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d245097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d245098 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d245098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d245098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d245099 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d245099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d245099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d245100 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d245100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d245100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79634 (p : Pattern) (ha : d209511 p = 1) (hb : d245106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d245101 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d245101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79633 q ha hb
    | true =>
      simp only [d209506, d245101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d245102 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d245102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d245102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d245103 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d245103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d245103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d245104 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d245104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d245104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d245105 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d245105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d245105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d245106 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d245106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d245106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79635 (p : Pattern) (ha : d209517 p = 1) (hb : d245112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d245107 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d245107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79634 q ha hb
    | true =>
      simp only [d209512, d245107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d245108 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d245108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d245108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d245109 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d245109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d245109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d245110 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d245110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d245110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d245111 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d245111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d245111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d245112 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d245112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d245112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79636 (p : Pattern) (ha : d209523 p = 1) (hb : d245118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d245113 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d245113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79635 q ha hb
    | true =>
      simp only [d209518, d245113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d245114 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d245114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d245114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d245115 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d245115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d245115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d245116 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d245116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d245116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d245117 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d245117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d245117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d245118 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d245118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d245118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79637 (p : Pattern) (ha : d209529 p = 1) (hb : d245124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d245119 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d245119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79636 q ha hb
    | true =>
      simp only [d209524, d245119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d245120 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d245120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d245120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d245121 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d245121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d245121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d245122 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d245122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d245122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d245123 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d245123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d245123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d245124 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d245124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d245124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79638 (p : Pattern) (ha : d209535 p = 1) (hb : d245130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d245125 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d245125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79637 q ha hb
    | true =>
      simp only [d209530, d245125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d245126 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d245126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d245126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d245127 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d245127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d245127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d245128 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d245128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d245128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d245129 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d245129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d245129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d245130 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d245130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d245130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79639 (p : Pattern) (ha : d209541 p = 1) (hb : d245136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d245131 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d245131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79638 q ha hb
    | true =>
      simp only [d209536, d245131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d245132 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d245132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d245132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d245133 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d245133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d245133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d245134 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d245134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d245134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d245135 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d245135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d245135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d245136 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d245136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d245136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79640 (p : Pattern) (ha : d241832 p = 1) (hb : d282071 p = 1) : d245139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30664 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79029 q ha hb
    | true =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30724 q = 1) (hb : d241832 q = 1) : d243808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30724, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30725 q = 1) (hb : d241832 q = 1) : d243809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30725, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30726 q = 1) (hb : d241832 q = 1) : d243810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30727 q = 1) (hb : d241832 q = 1) : d243811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d282071 q = 1) : d245139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282071, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282071, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro79641 (p : Pattern) (ha : d241832 p = 1) (hb : d282081 p = 1) : d245149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d241832 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30700 q = 1) (hb : d241832 q = 1) : d243784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79034 q ha hb
    | true =>
      simp only [d30700, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282077 q = 1) : d245145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282077, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282077, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282078 q = 1) : d245146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282078, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d282078, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282079 q = 1) : d245147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282079, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282079, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282080 q = 1) : d245148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282080, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282080, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d282081 q = 1) : d245149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282081, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282081, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro79642 (p : Pattern) (ha : d241832 p = 1) (hb : d282087 p = 1) : d245155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30729 q = 1) (hb : d241832 q = 1) : d243813 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79037 q ha hb
    | true =>
      simp only [d30729, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79038 q ha hb
  have h2 (q : Pattern) (ha : d30730 q = 1) (hb : d241832 q = 1) : d243814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30730, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282069 q = 1) : d245137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282069, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282069, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282070 q = 1) : d245138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282070, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282070, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282072 q = 1) : d245140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282072, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282072, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79640 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282073 q = 1) : d245141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282073, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282073, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d282074 q = 1) : d245142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282074, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282074, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d282075 q = 1) : d245143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282075, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282075, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d282076 q = 1) : d245144 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282076, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282076, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d282082 q = 1) : d245150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282082, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282082, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79641 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d282083 q = 1) : d245151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282083, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282083, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d282084 q = 1) : d245152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282084, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282084, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d282085 q = 1) : d245153 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282085, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282085, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d282086 q = 1) : d245154 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282086, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282086, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d282087 q = 1) : d245155 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282087, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282087, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79643 (p : Pattern) (ha : d241832 p = 1) (hb : d282093 p = 1) : d245161 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d241832 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d282088 q = 1) : d245156 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282088, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282088, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79642 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282089 q = 1) : d245157 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282089, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282089, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282090 q = 1) : d245158 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282090, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282090, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282091 q = 1) : d245159 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282091, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282091, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282092 q = 1) : d245160 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282092, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282092, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d282093 q = 1) : d245161 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282093, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282093, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro79644 (p : Pattern) (ha : d241832 p = 1) (hb : d282096 p = 1) : d245164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30940 q = 1) (hb : d241832 q = 1) : d243950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30940, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79066 q ha hb
    | true =>
      simp only [d30940, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79067 q ha hb
  have h2 (q : Pattern) (ha : d30941 q = 1) (hb : d241832 q = 1) : d243951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30941, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30942 q = 1) (hb : d241832 q = 1) : d243952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30942, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30943 q = 1) (hb : d241832 q = 1) : d243953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30944 q = 1) (hb : d241832 q = 1) : d243954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282096 q = 1) : d245164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282096, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282096, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro79645 (p : Pattern) (ha : d241832 p = 1) (hb : d282107 p = 1) : d245175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d282102 q = 1) : d245170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282102, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79098 q hb ha
    | true =>
      simp only [d282102, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79073 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d282103 q = 1) : d245171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282103, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282103, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282104 q = 1) : d245172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282104, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282104, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282105 q = 1) : d245173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282105, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282105, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282106 q = 1) : d245174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282106, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282106, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282107 q = 1) : d245175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282107, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282107, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79646 (p : Pattern) (ha : d241832 p = 1) (hb : d282113 p = 1) : d245181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30946 q = 1) (hb : d241832 q = 1) : d243956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79065 q ha hb
    | true =>
      simp only [d30946, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79068 q ha hb
  have h2 (q : Pattern) (ha : d30947 q = 1) (hb : d241832 q = 1) : d243957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30947, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282094 q = 1) : d245162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282094, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282094, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282095 q = 1) : d245163 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282095, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282095, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282097 q = 1) : d245165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282097, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282097, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79644 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282098 q = 1) : d245166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282098, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282098, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d282099 q = 1) : d245167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282099, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282099, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d282100 q = 1) : d245168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282100, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282100, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d282101 q = 1) : d245169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282101, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282101, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d282108 q = 1) : d245176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282108, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282108, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79645 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d282109 q = 1) : d245177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282109, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282109, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d282110 q = 1) : d245178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282110, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282110, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d282111 q = 1) : d245179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282111, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282111, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d282112 q = 1) : d245180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282112, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282112, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d282113 q = 1) : d245181 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282113, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282113, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79647 (p : Pattern) (ha : d241832 p = 1) (hb : d282119 p = 1) : d245187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d282114 q = 1) : d245182 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282114, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282114, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79646 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d282115 q = 1) : d245183 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282115, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282115, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282116 q = 1) : d245184 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282116, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282116, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282117 q = 1) : d245185 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282117, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282117, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282118 q = 1) : d245186 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282118, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282118, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282119 q = 1) : d245187 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282119, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282119, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79648 (p : Pattern) (ha : d241832 p = 1) (hb : d282123 p = 1) : d245191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31276 q = 1) (hb : d241832 q = 1) : d244155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79112 q ha hb
    | true =>
      simp only [d31276, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79113 q ha hb
  have h2 (q : Pattern) (ha : d31277 q = 1) (hb : d241832 q = 1) : d244156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31278 q = 1) (hb : d241832 q = 1) : d244157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31278, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31279 q = 1) (hb : d241832 q = 1) : d244158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31280 q = 1) (hb : d241832 q = 1) : d244159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282123 q = 1) : d245191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282123, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282123, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro79649 (p : Pattern) (ha : d241832 p = 1) (hb : d282134 p = 1) : d245202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d282129 q = 1) : d245197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282129, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79149 q hb ha
    | true =>
      simp only [d282129, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79121 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d282130 q = 1) : d245198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282130, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282130, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282131 q = 1) : d245199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282131, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282131, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282132 q = 1) : d245200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282132, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282132, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282133 q = 1) : d245201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282133, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282133, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282134 q = 1) : d245202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282134, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282134, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79650 (p : Pattern) (ha : d241832 p = 1) (hb : d282140 p = 1) : d245208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31282 q = 1) (hb : d241832 q = 1) : d244161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79111 q ha hb
    | true =>
      simp only [d31282, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79114 q ha hb
  have h2 (q : Pattern) (ha : d31283 q = 1) (hb : d241832 q = 1) : d244162 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31283, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282121 q = 1) : d245189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282121, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282121, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282122 q = 1) : d245190 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282122, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282122, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282124 q = 1) : d245192 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282124, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282124, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79648 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282125 q = 1) : d245193 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282125, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282125, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d282126 q = 1) : d245194 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282126, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282126, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d282127 q = 1) : d245195 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282127, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282127, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d282128 q = 1) : d245196 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282128, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282128, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d282135 q = 1) : d245203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282135, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282135, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79649 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d282136 q = 1) : d245204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282136, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282136, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d282137 q = 1) : d245205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282137, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282137, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d282138 q = 1) : d245206 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282138, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282138, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d282139 q = 1) : d245207 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282139, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282139, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d282140 q = 1) : d245208 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282140, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282140, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79651 (p : Pattern) (ha : d241832 p = 1) (hb : d282146 p = 1) : d245214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d282141 q = 1) : d245209 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282141, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282141, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79650 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d282142 q = 1) : d245210 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282142, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282142, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282143 q = 1) : d245211 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282143, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282143, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d282144 q = 1) : d245212 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282144, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282144, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d282145 q = 1) : d245213 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282145, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282145, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d282146 q = 1) : d245214 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282146, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282146, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79652 (p : Pattern) (ha : d241832 p = 1) (hb : d290378 p = 1) : d245219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31710 q = 1) (hb : d241832 q = 1) : d244379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79168 q ha hb
    | true =>
      simp only [d31710, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79169 q ha hb
  have h2 (q : Pattern) (ha : d31711 q = 1) (hb : d241832 q = 1) : d244380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31712 q = 1) (hb : d241832 q = 1) : d244381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31712, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31713 q = 1) (hb : d241832 q = 1) : d244382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31714 q = 1) (hb : d241832 q = 1) : d244383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290378 q = 1) : d245219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290378, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290378, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro79653 (p : Pattern) (ha : d241832 p = 1) (hb : d290389 p = 1) : d245230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290384 q = 1) : d245225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290384, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79208 q hb ha
    | true =>
      simp only [d290384, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79177 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290385 q = 1) : d245226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290385, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290385, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290386 q = 1) : d245227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290386, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290386, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290387 q = 1) : d245228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290387, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290387, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290388 q = 1) : d245229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290388, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290388, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290389 q = 1) : d245230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290389, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290389, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79654 (p : Pattern) (ha : d241832 p = 1) (hb : d290395 p = 1) : d245236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31716 q = 1) (hb : d241832 q = 1) : d244385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79167 q ha hb
    | true =>
      simp only [d31716, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79170 q ha hb
  have h2 (q : Pattern) (ha : d31717 q = 1) (hb : d241832 q = 1) : d244386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31717, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290376 q = 1) : d245217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290376, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290376, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290377 q = 1) : d245218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290377, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290377, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290379 q = 1) : d245220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290379, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290379, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79652 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290380 q = 1) : d245221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290380, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290380, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d290381 q = 1) : d245222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290381, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290381, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d290382 q = 1) : d245223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290382, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290382, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d290383 q = 1) : d245224 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290383, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290383, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d290390 q = 1) : d245231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290390, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290390, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79653 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d290391 q = 1) : d245232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290391, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290391, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d290392 q = 1) : d245233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290392, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290392, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d290393 q = 1) : d245234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290393, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290393, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d290394 q = 1) : d245235 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290394, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290394, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d290395 q = 1) : d245236 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290395, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290395, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79655 (p : Pattern) (ha : d241832 p = 1) (hb : d290401 p = 1) : d245242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290396 q = 1) : d245237 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290396, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290396, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79654 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290397 q = 1) : d245238 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290397, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290397, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290398 q = 1) : d245239 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290398, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290398, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290399 q = 1) : d245240 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290399, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290399, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290400 q = 1) : d245241 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290400, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290400, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290401 q = 1) : d245242 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290401, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290401, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79656 (p : Pattern) (ha : d241832 p = 1) (hb : d290407 p = 1) : d245248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32242 q = 1) (hb : d241832 q = 1) : d244631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79229 q ha hb
    | true =>
      simp only [d32242, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79230 q ha hb
  have h2 (q : Pattern) (ha : d32243 q = 1) (hb : d241832 q = 1) : d244632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32244 q = 1) (hb : d241832 q = 1) : d244633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32244, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32245 q = 1) (hb : d241832 q = 1) : d244634 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32246 q = 1) (hb : d241832 q = 1) : d244635 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290407 q = 1) : d245248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290407, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290407, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro79657 (p : Pattern) (ha : d241832 p = 1) (hb : d290418 p = 1) : d245259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290413 q = 1) : d245254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290413, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79268 q hb ha
    | true =>
      simp only [d290413, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79238 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290414 q = 1) : d245255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290414, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290414, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290415 q = 1) : d245256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290415, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290415, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290416 q = 1) : d245257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290416, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290416, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290417 q = 1) : d245258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290417, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290417, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290418 q = 1) : d245259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290418, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290418, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79658 (p : Pattern) (ha : d241832 p = 1) (hb : d290424 p = 1) : d245265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32248 q = 1) (hb : d241832 q = 1) : d244637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32248, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79228 q ha hb
    | true =>
      simp only [d32248, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79231 q ha hb
  have h2 (q : Pattern) (ha : d32249 q = 1) (hb : d241832 q = 1) : d244638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32249, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32249, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290405 q = 1) : d245246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290405, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290405, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290406 q = 1) : d245247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290406, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290406, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290408 q = 1) : d245249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290408, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290408, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79656 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290409 q = 1) : d245250 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290409, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290409, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d290410 q = 1) : d245251 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290410, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290410, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d290411 q = 1) : d245252 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290411, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290411, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d290412 q = 1) : d245253 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290412, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290412, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d290419 q = 1) : d245260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290419, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290419, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79657 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d290420 q = 1) : d245261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290420, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290420, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d290421 q = 1) : d245262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290421, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290421, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d290422 q = 1) : d245263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290422, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290422, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d290423 q = 1) : d245264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290423, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290423, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d290424 q = 1) : d245265 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290424, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290424, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79659 (p : Pattern) (ha : d241832 p = 1) (hb : d290430 p = 1) : d245271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290425 q = 1) : d245266 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290425, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290425, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79658 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290426 q = 1) : d245267 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290426, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290426, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290427 q = 1) : d245268 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290427, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290427, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290428 q = 1) : d245269 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290428, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290428, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290429 q = 1) : d245270 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290429, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290429, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290430 q = 1) : d245271 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290430, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290430, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79660 (p : Pattern) (ha : d241832 p = 1) (hb : d290437 p = 1) : d245278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32776 q = 1) (hb : d241832 q = 1) : d244884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32776, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79288 q ha hb
    | true =>
      simp only [d32776, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79289 q ha hb
  have h2 (q : Pattern) (ha : d32777 q = 1) (hb : d241832 q = 1) : d244885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32777, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32777, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32778 q = 1) (hb : d241832 q = 1) : d244886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32778, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32778, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32779 q = 1) (hb : d241832 q = 1) : d244887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32779, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32779, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32780 q = 1) (hb : d241832 q = 1) : d244888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32780, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32780, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290437 q = 1) : d245278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290437, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290437, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro79661 (p : Pattern) (ha : d241832 p = 1) (hb : d290448 p = 1) : d245289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290443 q = 1) : d245284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290443, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79326 q hb ha
    | true =>
      simp only [d290443, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79297 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290444 q = 1) : d245285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290444, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290444, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290445 q = 1) : d245286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290445, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290445, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290446 q = 1) : d245287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290446, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290446, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290447 q = 1) : d245288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290447, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290447, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290448 q = 1) : d245289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290448, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290448, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79662 (p : Pattern) (ha : d241832 p = 1) (hb : d290454 p = 1) : d245295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32782 q = 1) (hb : d241832 q = 1) : d244890 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32782, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79287 q ha hb
    | true =>
      simp only [d32782, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79290 q ha hb
  have h2 (q : Pattern) (ha : d32783 q = 1) (hb : d241832 q = 1) : d244891 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32783, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32783, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290435 q = 1) : d245276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290435, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290435, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290436 q = 1) : d245277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290436, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290436, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290438 q = 1) : d245279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290438, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290438, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79660 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290439 q = 1) : d245280 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290439, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290439, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d290440 q = 1) : d245281 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290440, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290440, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d290441 q = 1) : d245282 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290441, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290441, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d290442 q = 1) : d245283 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290442, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290442, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d290449 q = 1) : d245290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290449, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290449, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79661 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d290450 q = 1) : d245291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290450, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290450, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d290451 q = 1) : d245292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290451, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290451, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d290452 q = 1) : d245293 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290452, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290452, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d290453 q = 1) : d245294 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290453, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290453, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d290454 q = 1) : d245295 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290454, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290454, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79663 (p : Pattern) (ha : d241832 p = 1) (hb : d290460 p = 1) : d245301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290455 q = 1) : d245296 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290455, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290455, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79662 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290456 q = 1) : d245297 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290456, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290456, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290457 q = 1) : d245298 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290457, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290457, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290458 q = 1) : d245299 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290458, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290458, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290459 q = 1) : d245300 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290459, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290459, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290460 q = 1) : d245301 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290460, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290460, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79664 (p : Pattern) (ha : d241832 p = 1) (hb : d290466 p = 1) : d245307 p = 1 := by
  have h0 (q : Pattern) (ha : d241832 q = 1) (hb : d282120 q = 1) : d245188 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282120, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79643 q ha hb
    | true =>
      simp only [d282120, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79647 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d282147 q = 1) : d245215 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282147, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282147, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79651 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d282148 q = 1) : d245216 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d282148, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282148, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290402 q = 1) : d245243 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290402, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290402, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79655 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290403 q = 1) : d245244 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290403, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290403, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290404 q = 1) : d245245 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290404, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290404, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d290431 q = 1) : d245272 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290431, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290431, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79659 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d290432 q = 1) : d245273 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290432, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290432, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d290433 q = 1) : d245274 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290433, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290433, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d290434 q = 1) : d245275 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290434, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290434, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d290461 q = 1) : d245302 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290461, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290461, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79663 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d290462 q = 1) : d245303 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290462, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290462, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d290463 q = 1) : d245304 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290463, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290463, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d290464 q = 1) : d245305 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290464, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290464, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d290465 q = 1) : d245306 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d290465, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290465, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d290466 q = 1) : d245307 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d290466, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290466, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro79665 (p : Pattern) (ha : d241832 p = 1) (hb : d290472 p = 1) : d245313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290467 q = 1) : d245308 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d290467, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79664 q ha hb
    | true =>
      simp only [d290467, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290468 q = 1) : d245309 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d290468, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290468, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290469 q = 1) : d245310 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d290469, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290469, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290470 q = 1) : d245311 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d290470, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290470, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290471 q = 1) : d245312 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d290471, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290471, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290472 q = 1) : d245313 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d290472, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290472, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79666 (p : Pattern) (ha : d241832 p = 1) (hb : d290478 p = 1) : d245319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290473 q = 1) : d245314 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d290473, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79665 q ha hb
    | true =>
      simp only [d290473, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290474 q = 1) : d245315 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d290474, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290474, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290475 q = 1) : d245316 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d290475, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290475, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290476 q = 1) : d245317 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d290476, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290476, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290477 q = 1) : d245318 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d290477, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290477, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290478 q = 1) : d245319 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d290478, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290478, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79667 (p : Pattern) (ha : d241832 p = 1) (hb : d290484 p = 1) : d245325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290479 q = 1) : d245320 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d290479, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79666 q ha hb
    | true =>
      simp only [d290479, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290480 q = 1) : d245321 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d290480, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290480, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290481 q = 1) : d245322 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d290481, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290481, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290482 q = 1) : d245323 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d290482, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290482, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290483 q = 1) : d245324 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d290483, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290483, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290484 q = 1) : d245325 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d290484, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290484, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79668 (p : Pattern) (ha : d241832 p = 1) (hb : d290490 p = 1) : d245331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290485 q = 1) : d245326 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d290485, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79667 q ha hb
    | true =>
      simp only [d290485, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290486 q = 1) : d245327 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d290486, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290486, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290487 q = 1) : d245328 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d290487, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290487, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290488 q = 1) : d245329 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d290488, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290488, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290489 q = 1) : d245330 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d290489, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290489, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290490 q = 1) : d245331 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d290490, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290490, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79669 (p : Pattern) (ha : d241832 p = 1) (hb : d290496 p = 1) : d245337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290491 q = 1) : d245332 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d290491, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79668 q ha hb
    | true =>
      simp only [d290491, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290492 q = 1) : d245333 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d290492, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290492, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290493 q = 1) : d245334 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d290493, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290493, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290494 q = 1) : d245335 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d290494, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290494, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290495 q = 1) : d245336 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d290495, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290495, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290496 q = 1) : d245337 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d290496, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290496, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79670 (p : Pattern) (ha : d241832 p = 1) (hb : d290502 p = 1) : d245343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290497 q = 1) : d245338 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d290497, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79669 q ha hb
    | true =>
      simp only [d290497, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290498 q = 1) : d245339 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d290498, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290498, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290499 q = 1) : d245340 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d290499, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290499, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290500 q = 1) : d245341 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d290500, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290500, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290501 q = 1) : d245342 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d290501, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290501, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290502 q = 1) : d245343 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d290502, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290502, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79671 (p : Pattern) (ha : d241832 p = 1) (hb : d290508 p = 1) : d245349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d290503 q = 1) : d245344 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d290503, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79670 q ha hb
    | true =>
      simp only [d290503, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d290504 q = 1) : d245345 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d290504, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290504, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d290505 q = 1) : d245346 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d290505, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290505, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d290506 q = 1) : d245347 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d290506, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290506, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d290507 q = 1) : d245348 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d290507, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290507, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d290508 q = 1) : d245349 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d290508, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290508, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79672 (p : Pattern) (ha : d208161 p = 1) (hb : d243805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208048 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208048, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79343 q ha hb
    | true =>
      simp only [d208048, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d208151 q = 1) (hb : d243801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208151, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208151, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208158 q = 1) (hb : d243802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208158, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208158, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208159 q = 1) (hb : d243803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208159, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208159, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208160 q = 1) (hb : d243804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208160, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208160, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208161 q = 1) (hb : d243805 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208161, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208161, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79673 (p : Pattern) (ha : d208180 p = 1) (hb : d243812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208048 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208048, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79343 q ha hb
    | true =>
      simp only [d208048, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d208151 q = 1) (hb : d243801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208151, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208151, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208158 q = 1) (hb : d243802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208158, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208158, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208159 q = 1) (hb : d243803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208159, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208159, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208160 q = 1) (hb : d243804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208160, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208160, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208166 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208170 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208055 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208055, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79345 q ha hb
    | true =>
      simp only [d208055, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d208173 q = 1) (hb : d243808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208173, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208173, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208177 q = 1) (hb : d243809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208177, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208177, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208178 q = 1) (hb : d243810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208178, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208178, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208179 q = 1) (hb : d243811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208179, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208179, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208180 q = 1) (hb : d243812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208180, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208180, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79674 (p : Pattern) (ha : d208189 p = 1) (hb : d245139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208055 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208055, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79345 q ha hb
    | true =>
      simp only [d208055, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d208173 q = 1) (hb : d243808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208173, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208173, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208177 q = 1) (hb : d243809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208177, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208177, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208187 q = 1) (hb : d243810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208187, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208187, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208188 q = 1) (hb : d243811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208188, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208188, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208189 q = 1) (hb : d245139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208189, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208189, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79675 (p : Pattern) (ha : d208224 p = 1) (hb : d245149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208085 q = 1) (hb : d243784 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208085, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79349 q ha hb
    | true =>
      simp only [d208085, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d208214 q = 1) (hb : d245145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208214, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208214, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208220 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208221 q = 1) (hb : d245146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208221, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208221, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208222 q = 1) (hb : d245147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208222, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208222, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208223 q = 1) (hb : d245148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208223, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208223, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208224 q = 1) (hb : d245149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208224, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208224, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79676 (p : Pattern) (ha : d208230 p = 1) (hb : d245155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208116 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208181 q = 1) (hb : d243813 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208181, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79672 q ha hb
    | true =>
      simp only [d208181, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79673 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208184 q = 1) (hb : d243814 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208184, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208184, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208185 q = 1) (hb : d245137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208185, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208185, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208186 q = 1) (hb : d245138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208186, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208186, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208190 q = 1) (hb : d245140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208190, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208190, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79674 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208191 q = 1) (hb : d245141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208191, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208191, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208192 q = 1) (hb : d245142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208192, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208192, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208193 q = 1) (hb : d245143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208193, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208193, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208194 q = 1) (hb : d245144 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208194, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208194, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208225 q = 1) (hb : d245150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208225, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208225, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79675 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208226 q = 1) (hb : d245151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208226, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208226, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208227 q = 1) (hb : d245152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208227, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208227, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208228 q = 1) (hb : d245153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208228, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208228, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208229 q = 1) (hb : d245154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208229, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208229, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208230 q = 1) (hb : d245155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208230, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208230, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79677 (p : Pattern) (ha : d208236 p = 1) (hb : d245161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d208097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51140 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d208098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d208099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d208100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d208101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208231 q = 1) (hb : d245156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208231, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208231, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79676 q ha hb
  have h8 (q : Pattern) (ha : d208232 q = 1) (hb : d245157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208232, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208232, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208233 q = 1) (hb : d245158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208233, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208233, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208234 q = 1) (hb : d245159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208234, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208234, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208235 q = 1) (hb : d245160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208235, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208235, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208236 q = 1) (hb : d245161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208236, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d208236, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79678 (p : Pattern) (ha : d208322 p = 1) (hb : d243945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208254 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208254, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79377 q ha hb
    | true =>
      simp only [d208254, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79378 q ha hb
  have h5 (q : Pattern) (ha : d208312 q = 1) (hb : d243941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208312, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208312, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208319 q = 1) (hb : d243942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208319, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208319, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208320 q = 1) (hb : d243943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208320, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208320, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208321 q = 1) (hb : d243944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208321, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208321, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208322 q = 1) (hb : d243945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208322, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208322, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79679 (p : Pattern) (ha : d208343 p = 1) (hb : d243955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208254 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208254, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79377 q ha hb
    | true =>
      simp only [d208254, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79378 q ha hb
  have h4 (q : Pattern) (ha : d208312 q = 1) (hb : d243941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208312, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208312, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208319 q = 1) (hb : d243942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208319, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208319, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208320 q = 1) (hb : d243943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208320, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208320, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208321 q = 1) (hb : d243944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208321, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208321, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208328 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208333 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208264 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208264, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79380 q ha hb
    | true =>
      simp only [d208264, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79381 q ha hb
  have h13 (q : Pattern) (ha : d208336 q = 1) (hb : d243951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208336, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208336, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208340 q = 1) (hb : d243952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208340, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208340, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208341 q = 1) (hb : d243953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208341, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208341, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208342 q = 1) (hb : d243954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208342, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208342, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208343 q = 1) (hb : d243955 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208343, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208343, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79680 (p : Pattern) (ha : d208363 p = 1) (hb : d245164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208264 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208264, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79380 q ha hb
    | true =>
      simp only [d208264, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79381 q ha hb
  have h3 (q : Pattern) (ha : d208336 q = 1) (hb : d243951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208336, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208336, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208340 q = 1) (hb : d243952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208340, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208340, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208361 q = 1) (hb : d243953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208361, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208361, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208362 q = 1) (hb : d243954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208362, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208362, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208363 q = 1) (hb : d245164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208363, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208363, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79681 (p : Pattern) (ha : d208418 p = 1) (hb : d245175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208407 q = 1) (hb : d245170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208407, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79408 q ha hb
    | true =>
      simp only [d208407, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79411 q ha hb
  have h3 (q : Pattern) (ha : d208408 q = 1) (hb : d245171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208408, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208408, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208414 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208415 q = 1) (hb : d245172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208415, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208415, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208416 q = 1) (hb : d245173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208416, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208416, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208417 q = 1) (hb : d245174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208417, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208417, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208418 q = 1) (hb : d245175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208418, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208418, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79682 (p : Pattern) (ha : d208431 p = 1) (hb : d245181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208344 q = 1) (hb : d243956 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208344, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79678 q ha hb
    | true =>
      simp only [d208344, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79679 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208358 q = 1) (hb : d243957 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208358, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208358, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208359 q = 1) (hb : d245162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208359, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208359, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208360 q = 1) (hb : d245163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208360, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208360, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208364 q = 1) (hb : d245165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208364, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208364, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79680 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208366 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208367 q = 1) (hb : d245166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208367, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208367, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208368 q = 1) (hb : d245167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208368, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208368, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208369 q = 1) (hb : d245168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208369, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208369, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208370 q = 1) (hb : d245169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208370, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208370, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208419 q = 1) (hb : d245176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208419, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208419, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79681 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208426 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208427 q = 1) (hb : d245177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208427, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208427, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208428 q = 1) (hb : d245178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208428, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208428, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208429 q = 1) (hb : d245179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208429, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208429, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208430 q = 1) (hb : d245180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208430, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208430, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208431 q = 1) (hb : d245181 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208431, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208431, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79683 (p : Pattern) (ha : d208437 p = 1) (hb : d245187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208432 q = 1) (hb : d245182 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208432, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208432, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79682 q ha hb
  have h2 (q : Pattern) (ha : d208433 q = 1) (hb : d245183 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208433, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208433, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208434 q = 1) (hb : d245184 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208434, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208434, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208435 q = 1) (hb : d245185 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208435, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208435, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208436 q = 1) (hb : d245186 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208436, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208436, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208437 q = 1) (hb : d245187 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208437, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208437, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79684 (p : Pattern) (ha : d208534 p = 1) (hb : d244150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208466 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208466, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79421 q ha hb
    | true =>
      simp only [d208466, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79422 q ha hb
  have h5 (q : Pattern) (ha : d208524 q = 1) (hb : d244146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208524, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208524, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208531 q = 1) (hb : d244147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208531, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208531, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208532 q = 1) (hb : d244148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208532, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208532, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208533 q = 1) (hb : d244149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208533, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208533, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208534 q = 1) (hb : d244150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208534, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208534, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79685 (p : Pattern) (ha : d208555 p = 1) (hb : d244160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208466 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208466, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79421 q ha hb
    | true =>
      simp only [d208466, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79422 q ha hb
  have h4 (q : Pattern) (ha : d208524 q = 1) (hb : d244146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208524, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208524, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208531 q = 1) (hb : d244147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208531, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208531, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208532 q = 1) (hb : d244148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208532, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208532, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208533 q = 1) (hb : d244149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208533, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208533, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208545 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208476 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208476, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79424 q ha hb
    | true =>
      simp only [d208476, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79425 q ha hb
  have h13 (q : Pattern) (ha : d208548 q = 1) (hb : d244156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208548, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208548, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208552 q = 1) (hb : d244157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208552, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208552, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208553 q = 1) (hb : d244158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208553, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208553, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208554 q = 1) (hb : d244159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208554, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208554, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208555 q = 1) (hb : d244160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208555, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208555, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79686 (p : Pattern) (ha : d208575 p = 1) (hb : d245191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208476 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208476, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79424 q ha hb
    | true =>
      simp only [d208476, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79425 q ha hb
  have h3 (q : Pattern) (ha : d208548 q = 1) (hb : d244156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208548, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208548, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208552 q = 1) (hb : d244157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208552, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208552, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208573 q = 1) (hb : d244158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208573, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208573, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208574 q = 1) (hb : d244159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208574, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208574, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208575 q = 1) (hb : d245191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208575, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208575, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79687 (p : Pattern) (ha : d208640 p = 1) (hb : d245202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208629 q = 1) (hb : d245197 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208629, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79455 q ha hb
    | true =>
      simp only [d208629, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79458 q ha hb
  have h3 (q : Pattern) (ha : d208630 q = 1) (hb : d245198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208630, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208630, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208636 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208637 q = 1) (hb : d245199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208637, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208637, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208638 q = 1) (hb : d245200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208638, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208638, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208639 q = 1) (hb : d245201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208639, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208639, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208640 q = 1) (hb : d245202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208640, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208640, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79688 (p : Pattern) (ha : d208653 p = 1) (hb : d245208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208556 q = 1) (hb : d244161 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208556, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79684 q ha hb
    | true =>
      simp only [d208556, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79685 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208569 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208570 q = 1) (hb : d244162 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208570, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208570, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208571 q = 1) (hb : d245189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208571, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208571, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208572 q = 1) (hb : d245190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208572, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208572, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208576 q = 1) (hb : d245192 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208576, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208576, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79686 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208578 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208579 q = 1) (hb : d245193 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208579, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208579, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208580 q = 1) (hb : d245194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208580, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208580, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208581 q = 1) (hb : d245195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208581, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208581, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208582 q = 1) (hb : d245196 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208582, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208582, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208641 q = 1) (hb : d245203 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208641, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208641, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79687 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208648 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208649 q = 1) (hb : d245204 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208649, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208649, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208650 q = 1) (hb : d245205 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208650, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208650, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208651 q = 1) (hb : d245206 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208651, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208651, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208652 q = 1) (hb : d245207 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208652, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208652, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208653 q = 1) (hb : d245208 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208653, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208653, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79689 (p : Pattern) (ha : d208659 p = 1) (hb : d245214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208654 q = 1) (hb : d245209 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208654, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208654, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79688 q ha hb
  have h2 (q : Pattern) (ha : d208655 q = 1) (hb : d245210 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208655, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208655, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208656 q = 1) (hb : d245211 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208656, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208656, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208657 q = 1) (hb : d245212 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208657, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208657, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208658 q = 1) (hb : d245213 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208658, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208658, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208659 q = 1) (hb : d245214 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208659, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208659, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79690 (p : Pattern) (ha : d208790 p = 1) (hb : d244374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208713 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208713, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79470 q ha hb
    | true =>
      simp only [d208713, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79471 q ha hb
  have h5 (q : Pattern) (ha : d208771 q = 1) (hb : d244370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208771, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208771, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208787 q = 1) (hb : d244371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208787, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208787, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208788 q = 1) (hb : d244372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208788, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208788, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208789 q = 1) (hb : d244373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208789, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208789, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208790 q = 1) (hb : d244374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208790, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208790, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79691 (p : Pattern) (ha : d208811 p = 1) (hb : d244384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208713 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208713, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79470 q ha hb
    | true =>
      simp only [d208713, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79471 q ha hb
  have h4 (q : Pattern) (ha : d208771 q = 1) (hb : d244370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208771, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208771, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208787 q = 1) (hb : d244371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208787, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208787, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208788 q = 1) (hb : d244372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208788, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208788, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208789 q = 1) (hb : d244373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208789, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208789, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208796 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208723 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208723, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79473 q ha hb
    | true =>
      simp only [d208723, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79474 q ha hb
  have h13 (q : Pattern) (ha : d208804 q = 1) (hb : d244380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208804, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208804, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208808 q = 1) (hb : d244381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208808, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208808, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208809 q = 1) (hb : d244382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208809, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208809, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208810 q = 1) (hb : d244383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208810, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208810, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208811 q = 1) (hb : d244384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208811, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208811, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79692 (p : Pattern) (ha : d208831 p = 1) (hb : d245219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208723 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208723, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79473 q ha hb
    | true =>
      simp only [d208723, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79474 q ha hb
  have h3 (q : Pattern) (ha : d208804 q = 1) (hb : d244380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208804, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208804, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208808 q = 1) (hb : d244381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208808, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208808, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208829 q = 1) (hb : d244382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208829, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208829, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208830 q = 1) (hb : d244383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208830, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208830, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208831 q = 1) (hb : d245219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208831, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208831, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79693 (p : Pattern) (ha : d208920 p = 1) (hb : d245230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208895 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208900 q = 1) (hb : d245225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208900, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79509 q ha hb
    | true =>
      simp only [d208900, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79515 q ha hb
  have h3 (q : Pattern) (ha : d208901 q = 1) (hb : d245226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208901, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208901, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208917 q = 1) (hb : d245227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208917, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208917, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208918 q = 1) (hb : d245228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208918, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208918, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208919 q = 1) (hb : d245229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208919, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208919, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208920 q = 1) (hb : d245230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208920, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208920, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79694 (p : Pattern) (ha : d208933 p = 1) (hb : d245236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208812 q = 1) (hb : d244385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208812, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79690 q ha hb
    | true =>
      simp only [d208812, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79691 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208825 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208826 q = 1) (hb : d244386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208826, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208826, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208827 q = 1) (hb : d245217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208827, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208827, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208828 q = 1) (hb : d245218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208828, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208828, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208832 q = 1) (hb : d245220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208832, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208832, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79692 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208834 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208835 q = 1) (hb : d245221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208835, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208835, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208836 q = 1) (hb : d245222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208836, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208836, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208837 q = 1) (hb : d245223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208837, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208837, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208838 q = 1) (hb : d245224 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208838, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208838, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208921 q = 1) (hb : d245231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208921, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208921, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79693 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208928 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208929 q = 1) (hb : d245232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208929, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208929, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208930 q = 1) (hb : d245233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208930, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208930, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208931 q = 1) (hb : d245234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208931, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208931, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208932 q = 1) (hb : d245235 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208932, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208932, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208933 q = 1) (hb : d245236 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208933, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208933, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79695 (p : Pattern) (ha : d208939 p = 1) (hb : d245242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208934 q = 1) (hb : d245237 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208934, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208934, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79694 q ha hb
  have h2 (q : Pattern) (ha : d208935 q = 1) (hb : d245238 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208935, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208935, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208936 q = 1) (hb : d245239 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208936, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208936, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208937 q = 1) (hb : d245240 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208937, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208937, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208938 q = 1) (hb : d245241 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208938, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208938, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208939 q = 1) (hb : d245242 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208939, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208939, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79696 (p : Pattern) (ha : d209073 p = 1) (hb : d244626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208996 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
    | true =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
  have h5 (q : Pattern) (ha : d209054 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209054, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209070 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209070, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d209071 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209071, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209072 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209072, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209073 q = 1) (hb : d244626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209073, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209073, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79697 (p : Pattern) (ha : d209094 p = 1) (hb : d244636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208996 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79527 q ha hb
    | true =>
      simp only [d208996, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79528 q ha hb
  have h4 (q : Pattern) (ha : d209054 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209054, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209070 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209070, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209071 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209071, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209072 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209072, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209079 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209084 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d209006 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79530 q ha hb
    | true =>
      simp only [d209006, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79531 q ha hb
  have h13 (q : Pattern) (ha : d209087 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d209087, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209091 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209091, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209092 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209092, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209092, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209093 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209093, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209093, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209094 q = 1) (hb : d244636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209094, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209094, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79698 (p : Pattern) (ha : d209114 p = 1) (hb : d245248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209006 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79530 q ha hb
    | true =>
      simp only [d209006, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79531 q ha hb
  have h3 (q : Pattern) (ha : d209087 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209087, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209091 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209091, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209112 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209112, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209112, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209113 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209113, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209113, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209114 q = 1) (hb : d245248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79699 (p : Pattern) (ha : d209203 p = 1) (hb : d245259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209178 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209183 q = 1) (hb : d245254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209183, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79566 q ha hb
    | true =>
      simp only [d209183, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79572 q ha hb
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d245255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209184, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209199 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209200 q = 1) (hb : d245256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209201 q = 1) (hb : d245257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209202 q = 1) (hb : d245258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209203 q = 1) (hb : d245259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79700 (p : Pattern) (ha : d209216 p = 1) (hb : d245265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209095 q = 1) (hb : d244637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209095, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79696 q ha hb
    | true =>
      simp only [d209095, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79697 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209109 q = 1) (hb : d244638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209109, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209109, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209110 q = 1) (hb : d245246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209110, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209111 q = 1) (hb : d245247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209111, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209115 q = 1) (hb : d245249 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209115, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79698 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209117 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209118 q = 1) (hb : d245250 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209118, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209119 q = 1) (hb : d245251 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209119, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209120 q = 1) (hb : d245252 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209120, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209121 q = 1) (hb : d245253 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209121, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209204 q = 1) (hb : d245260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209204, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79699 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209212 q = 1) (hb : d245261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209212, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209213 q = 1) (hb : d245262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209213, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209214 q = 1) (hb : d245263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209214, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209215 q = 1) (hb : d245264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209215, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209216 q = 1) (hb : d245265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209216, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79701 (p : Pattern) (ha : d209222 p = 1) (hb : d245271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d245266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79700 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d245267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d245268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d245269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d245270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d245271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79702 (p : Pattern) (ha : d209348 p = 1) (hb : d244879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d209278 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
    | true =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
  have h5 (q : Pattern) (ha : d209329 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209329, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209345 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209345, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d209346 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209346, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209347 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209347, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209348 q = 1) (hb : d244879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79703 (p : Pattern) (ha : d209369 p = 1) (hb : d244889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209278 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79584 q ha hb
    | true =>
      simp only [d209278, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79585 q ha hb
  have h4 (q : Pattern) (ha : d209329 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209329, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209345 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209345, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209346 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209346, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209347 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209347, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209354 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d209288 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79587 q ha hb
    | true =>
      simp only [d209288, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79588 q ha hb
  have h13 (q : Pattern) (ha : d209362 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d209362, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209366 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209366, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209367 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209367, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209368 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209368, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209369 q = 1) (hb : d244889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209369, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79704 (p : Pattern) (ha : d209389 p = 1) (hb : d245278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209288 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79587 q ha hb
    | true =>
      simp only [d209288, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79588 q ha hb
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209362, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209366 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209387 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209388 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209389 q = 1) (hb : d245278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79705 (p : Pattern) (ha : d209474 p = 1) (hb : d245289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209454 q = 1) (hb : d245284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209454, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79622 q ha hb
    | true =>
      simp only [d209454, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79628 q ha hb
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d245285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209455, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209470 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209471 q = 1) (hb : d245286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209472 q = 1) (hb : d245287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209473 q = 1) (hb : d245288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209474 q = 1) (hb : d245289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79706 (p : Pattern) (ha : d209487 p = 1) (hb : d245295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209296 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209370 q = 1) (hb : d244890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79702 q ha hb
    | true =>
      simp only [d209370, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79703 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209384 q = 1) (hb : d244891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209384, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209385 q = 1) (hb : d245276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209385, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209386 q = 1) (hb : d245277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209386, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209390 q = 1) (hb : d245279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209390, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79704 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209392 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209393 q = 1) (hb : d245280 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209393, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209394 q = 1) (hb : d245281 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209394, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209395 q = 1) (hb : d245282 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209395, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209396 q = 1) (hb : d245283 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209396, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209475 q = 1) (hb : d245290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209475, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79705 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209482 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209483 q = 1) (hb : d245291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209483, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209484 q = 1) (hb : d245292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209484, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209485 q = 1) (hb : d245293 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209485, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209486 q = 1) (hb : d245294 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209486, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209487 q = 1) (hb : d245295 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209487, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79707 (p : Pattern) (ha : d209493 p = 1) (hb : d245301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d245296 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79706 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d245297 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d245298 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d245299 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d245300 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d245301 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79708 (p : Pattern) (ha : d209499 p = 1) (hb : d245307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d245188 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79677 q ha hb
    | true =>
      simp only [d208438, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79683 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d245215 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79689 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d245216 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d245243 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79695 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d245244 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d245245 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d245272 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79701 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d245273 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d245274 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d245275 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d245302 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79707 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d245303 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d245304 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d245305 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d245306 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d245307 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro79709 (p : Pattern) (ha : d209505 p = 1) (hb : d245313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d245308 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79708 q ha hb
    | true =>
      simp only [d209500, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d245309 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d245310 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d245311 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d245312 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d245313 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79710 (p : Pattern) (ha : d209511 p = 1) (hb : d245319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d245314 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79709 q ha hb
    | true =>
      simp only [d209506, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d245315 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d245316 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d245317 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d245318 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d245319 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79711 (p : Pattern) (ha : d209517 p = 1) (hb : d245325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d245320 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79710 q ha hb
    | true =>
      simp only [d209512, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d245321 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d245322 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d245323 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d245324 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d245325 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79712 (p : Pattern) (ha : d209523 p = 1) (hb : d245331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d245326 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79711 q ha hb
    | true =>
      simp only [d209518, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d245327 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d245328 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d245329 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d245330 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d245331 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79713 (p : Pattern) (ha : d209529 p = 1) (hb : d245337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d245332 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79712 q ha hb
    | true =>
      simp only [d209524, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d245333 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d245334 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d245335 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d245336 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d245337 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79714 (p : Pattern) (ha : d209535 p = 1) (hb : d245343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d245338 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79713 q ha hb
    | true =>
      simp only [d209530, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d245339 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d245340 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d245341 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d245342 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d245343 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79715 (p : Pattern) (ha : d209541 p = 1) (hb : d245349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d245344 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79714 q ha hb
    | true =>
      simp only [d209536, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d245345 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d245346 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d245347 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d245348 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d245349 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro79716 (p : Pattern) (ha : d211124 p = 1) (hb : d243805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211120 q = 1) (hb : d243801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211120, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211121 q = 1) (hb : d243802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211121, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211122 q = 1) (hb : d243803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211122, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211123 q = 1) (hb : d243804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211123, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211124 q = 1) (hb : d243805 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211124, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211124, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79717 (p : Pattern) (ha : d211129 p = 1) (hb : d243812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211120 q = 1) (hb : d243801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211120, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211121 q = 1) (hb : d243802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211121, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211122 q = 1) (hb : d243803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211122, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211123 q = 1) (hb : d243804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211123, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23279 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23283 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211125 q = 1) (hb : d243808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211125, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211126 q = 1) (hb : d243809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211126, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211127 q = 1) (hb : d243810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211127, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211127, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211128 q = 1) (hb : d243811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211128, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211128, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211129 q = 1) (hb : d243812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211129, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211129, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79718 (p : Pattern) (ha : d211136 p = 1) (hb : d245139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211125 q = 1) (hb : d243808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211125, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211126 q = 1) (hb : d243809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211126, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211134 q = 1) (hb : d243810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211134, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211134, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211135 q = 1) (hb : d243811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211135, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211135, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211136 q = 1) (hb : d245139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211136, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211136, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79719 (p : Pattern) (ha : d211146 p = 1) (hb : d245149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211142 q = 1) (hb : d245145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211142, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211142, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23349 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211143 q = 1) (hb : d245146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211143, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211143, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211144 q = 1) (hb : d245147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211144, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211144, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211145 q = 1) (hb : d245148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211145, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211145, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211146 q = 1) (hb : d245149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211146, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211146, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79720 (p : Pattern) (ha : d211152 p = 1) (hb : d245155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211130 q = 1) (hb : d243813 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211130, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79716 q ha hb
    | true =>
      simp only [d211130, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79717 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211131 q = 1) (hb : d243814 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211131, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211131, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211132 q = 1) (hb : d245137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211132, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211132, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211133 q = 1) (hb : d245138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211133, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211133, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211137 q = 1) (hb : d245140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211137, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211137, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79718 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211138 q = 1) (hb : d245141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211138, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211138, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211139 q = 1) (hb : d245142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211139, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211139, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211140 q = 1) (hb : d245143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211140, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211140, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211141 q = 1) (hb : d245144 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211141, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211141, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211147 q = 1) (hb : d245150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211147, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211147, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79719 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211148 q = 1) (hb : d245151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211148, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211148, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211149 q = 1) (hb : d245152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211149, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211149, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211150 q = 1) (hb : d245153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211150, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211150, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211151 q = 1) (hb : d245154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211151, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211151, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211152 q = 1) (hb : d245155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211152, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211152, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79721 (p : Pattern) (ha : d211158 p = 1) (hb : d245161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d211115 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51189 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d211116 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d211117 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d211118 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d211119 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211153 q = 1) (hb : d245156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211153, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211153, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79720 q ha hb
  have h8 (q : Pattern) (ha : d211154 q = 1) (hb : d245157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211154, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211154, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211155 q = 1) (hb : d245158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211155, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211155, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211156 q = 1) (hb : d245159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211156, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211156, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211157 q = 1) (hb : d245160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211157, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211157, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d211158 q = 1) (hb : d245161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211158, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d211158, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79722 (p : Pattern) (ha : d211163 p = 1) (hb : d243945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211159 q = 1) (hb : d243941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211159, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211160 q = 1) (hb : d243942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211160, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211161 q = 1) (hb : d243943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211161, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211162 q = 1) (hb : d243944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211162, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211163 q = 1) (hb : d243945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211163, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211163, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79723 (p : Pattern) (ha : d211168 p = 1) (hb : d243955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211159 q = 1) (hb : d243941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211159, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211160 q = 1) (hb : d243942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211160, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211161 q = 1) (hb : d243943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211161, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211162 q = 1) (hb : d243944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211162, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211164 q = 1) (hb : d243951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211164, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211165 q = 1) (hb : d243952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211165, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211166 q = 1) (hb : d243953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211166, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211166, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211167 q = 1) (hb : d243954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211167, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211167, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211168 q = 1) (hb : d243955 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211168, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211168, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79724 (p : Pattern) (ha : d211175 p = 1) (hb : d245164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211164 q = 1) (hb : d243951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211164, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211165 q = 1) (hb : d243952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211165, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211173 q = 1) (hb : d243953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211173, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211173, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211174 q = 1) (hb : d243954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211174, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211174, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211175 q = 1) (hb : d245164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211175, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211175, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79725 (p : Pattern) (ha : d211185 p = 1) (hb : d245175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245170 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211181 q = 1) (hb : d245171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211181, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211181, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23600 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211182 q = 1) (hb : d245172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211182, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211182, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211183 q = 1) (hb : d245173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211183, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211183, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211184 q = 1) (hb : d245174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211184, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211184, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211185 q = 1) (hb : d245175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211185, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211185, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79726 (p : Pattern) (ha : d211191 p = 1) (hb : d245181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211169 q = 1) (hb : d243956 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211169, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79722 q ha hb
    | true =>
      simp only [d211169, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79723 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211170 q = 1) (hb : d243957 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211170, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211170, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211171 q = 1) (hb : d245162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211171, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211171, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211172 q = 1) (hb : d245163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211172, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211172, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211176 q = 1) (hb : d245165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211176, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211176, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79724 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211177 q = 1) (hb : d245166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211177, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211177, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211178 q = 1) (hb : d245167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211178, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211178, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211179 q = 1) (hb : d245168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211179, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211179, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211180 q = 1) (hb : d245169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211180, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211180, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211186 q = 1) (hb : d245176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211186, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211186, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79725 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23616 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211187 q = 1) (hb : d245177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211187, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211187, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211188 q = 1) (hb : d245178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211188, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211188, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211189 q = 1) (hb : d245179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211189, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211189, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211190 q = 1) (hb : d245180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211190, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211190, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211191 q = 1) (hb : d245181 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211191, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211191, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79727 (p : Pattern) (ha : d211197 p = 1) (hb : d245187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211192 q = 1) (hb : d245182 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211192, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211192, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79726 q ha hb
  have h2 (q : Pattern) (ha : d211193 q = 1) (hb : d245183 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211193, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211193, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211194 q = 1) (hb : d245184 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211194, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211194, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211195 q = 1) (hb : d245185 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211195, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211195, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211196 q = 1) (hb : d245186 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211196, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211196, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211197 q = 1) (hb : d245187 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211197, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211197, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79728 (p : Pattern) (ha : d211203 p = 1) (hb : d244150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211199 q = 1) (hb : d244146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211199, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211200 q = 1) (hb : d244147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211200, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211201 q = 1) (hb : d244148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211201, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211202 q = 1) (hb : d244149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211202, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211203 q = 1) (hb : d244150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211203, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211203, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79729 (p : Pattern) (ha : d211208 p = 1) (hb : d244160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211199 q = 1) (hb : d244146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211199, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211200 q = 1) (hb : d244147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211200, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211201 q = 1) (hb : d244148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211201, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211202 q = 1) (hb : d244149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211202, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23768 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23773 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211204 q = 1) (hb : d244156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211204, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211205 q = 1) (hb : d244157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211205, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211206 q = 1) (hb : d244158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211206, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211206, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211207 q = 1) (hb : d244159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211207, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211207, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211208 q = 1) (hb : d244160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211208, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211208, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79730 (p : Pattern) (ha : d211215 p = 1) (hb : d245191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211204 q = 1) (hb : d244156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211204, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211205 q = 1) (hb : d244157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211205, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211213 q = 1) (hb : d244158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211213, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211213, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211214 q = 1) (hb : d244159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211214, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211214, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211215 q = 1) (hb : d245191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211215, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211215, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79731 (p : Pattern) (ha : d211225 p = 1) (hb : d245202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245197 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211221 q = 1) (hb : d245198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211221, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211221, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23897 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211222 q = 1) (hb : d245199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211222, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211222, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211223 q = 1) (hb : d245200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211223, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211223, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211224 q = 1) (hb : d245201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211224, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211224, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211225 q = 1) (hb : d245202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211225, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211225, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79732 (p : Pattern) (ha : d211231 p = 1) (hb : d245208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211209 q = 1) (hb : d244161 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211209, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79728 q ha hb
    | true =>
      simp only [d211209, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79729 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211210 q = 1) (hb : d244162 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211210, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211210, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211211 q = 1) (hb : d245189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211211, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211211, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211212 q = 1) (hb : d245190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211212, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211212, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211216 q = 1) (hb : d245192 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211216, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211216, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79730 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23809 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211217 q = 1) (hb : d245193 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211217, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211217, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211218 q = 1) (hb : d245194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211218, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211218, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211219 q = 1) (hb : d245195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211219, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211219, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211220 q = 1) (hb : d245196 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211220, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211220, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211226 q = 1) (hb : d245203 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211226, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211226, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79731 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23913 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211227 q = 1) (hb : d245204 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211227, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211227, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211228 q = 1) (hb : d245205 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211228, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211228, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211229 q = 1) (hb : d245206 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211229, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211229, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211230 q = 1) (hb : d245207 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211230, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211230, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211231 q = 1) (hb : d245208 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211231, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211231, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79733 (p : Pattern) (ha : d211237 p = 1) (hb : d245214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211232 q = 1) (hb : d245209 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211232, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211232, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79732 q ha hb
  have h2 (q : Pattern) (ha : d211233 q = 1) (hb : d245210 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211233, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211233, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211234 q = 1) (hb : d245211 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211234, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211234, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211235 q = 1) (hb : d245212 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211235, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211235, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211236 q = 1) (hb : d245213 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211236, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211236, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211237 q = 1) (hb : d245214 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211237, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211237, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79734 (p : Pattern) (ha : d211244 p = 1) (hb : d244374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211240 q = 1) (hb : d244370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211240, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211241 q = 1) (hb : d244371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211241, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211242 q = 1) (hb : d244372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211242, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211243 q = 1) (hb : d244373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211243, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211244 q = 1) (hb : d244374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211244, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211244, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79735 (p : Pattern) (ha : d211249 p = 1) (hb : d244384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211240 q = 1) (hb : d244370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211240, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211241 q = 1) (hb : d244371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211241, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211242 q = 1) (hb : d244372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211242, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211243 q = 1) (hb : d244373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211243, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24115 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24120 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211245 q = 1) (hb : d244380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211245, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211246 q = 1) (hb : d244381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211246, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211247 q = 1) (hb : d244382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211247, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211247, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211248 q = 1) (hb : d244383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211248, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211248, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211249 q = 1) (hb : d244384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211249, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211249, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79736 (p : Pattern) (ha : d211256 p = 1) (hb : d245219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211245 q = 1) (hb : d244380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211245, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211246 q = 1) (hb : d244381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211246, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211254 q = 1) (hb : d244382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211254, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211254, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211255 q = 1) (hb : d244383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211255, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211255, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211256 q = 1) (hb : d245219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211256, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211256, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79737 (p : Pattern) (ha : d211266 p = 1) (hb : d245230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24217 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211262 q = 1) (hb : d245226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211262, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211262, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211263 q = 1) (hb : d245227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211263, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211263, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211264 q = 1) (hb : d245228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211264, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211264, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211265 q = 1) (hb : d245229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211265, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211265, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211266 q = 1) (hb : d245230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211266, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211266, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79738 (p : Pattern) (ha : d211272 p = 1) (hb : d245236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211250 q = 1) (hb : d244385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211250, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79734 q ha hb
    | true =>
      simp only [d211250, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79735 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24147 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211251 q = 1) (hb : d244386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211251, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211251, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211252 q = 1) (hb : d245217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211252, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211252, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211253 q = 1) (hb : d245218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211253, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211253, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211257 q = 1) (hb : d245220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211257, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211257, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79736 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24156 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211258 q = 1) (hb : d245221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211258, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211258, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211259 q = 1) (hb : d245222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211259, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211259, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211260 q = 1) (hb : d245223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211260, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211260, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211261 q = 1) (hb : d245224 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211261, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211261, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211267 q = 1) (hb : d245231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211267, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211267, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79737 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24292 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211268 q = 1) (hb : d245232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211268, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211268, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211269 q = 1) (hb : d245233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211269, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211269, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211270 q = 1) (hb : d245234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211270, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211270, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211271 q = 1) (hb : d245235 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211271, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211271, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211272 q = 1) (hb : d245236 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211272, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211272, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79739 (p : Pattern) (ha : d211278 p = 1) (hb : d245242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211273 q = 1) (hb : d245237 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211273, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211273, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79738 q ha hb
  have h2 (q : Pattern) (ha : d211274 q = 1) (hb : d245238 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211274, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211274, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211275 q = 1) (hb : d245239 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211275, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211275, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211276 q = 1) (hb : d245240 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211276, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211276, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211277 q = 1) (hb : d245241 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211277, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211277, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211278 q = 1) (hb : d245242 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211278, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211278, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79740 (p : Pattern) (ha : d211286 p = 1) (hb : d244626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211282 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211282, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211282, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211283 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211283, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211283, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211284 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211284, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211284, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211285 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211285, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211285, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211286 q = 1) (hb : d244626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211286, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211286, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79741 (p : Pattern) (ha : d211291 p = 1) (hb : d244636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211282 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211282, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211282, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211283 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211283, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211283, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211284 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211284, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211284, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211285 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211285, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211285, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24502 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211287 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211287, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211287, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211288 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211288, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211288, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211289 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211289, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211289, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211290 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211290, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211290, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211291 q = 1) (hb : d244636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211291, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211291, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79742 (p : Pattern) (ha : d211298 p = 1) (hb : d245248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211287 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211287, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211287, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211288 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211288, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211288, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211296 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211296, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211296, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211297 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211297, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211297, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211298 q = 1) (hb : d245248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211298, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211298, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79743 (p : Pattern) (ha : d211308 p = 1) (hb : d245259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245254 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211304 q = 1) (hb : d245255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211304, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211304, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24658 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211305 q = 1) (hb : d245256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211305, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211305, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211306 q = 1) (hb : d245257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211306, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211306, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211307 q = 1) (hb : d245258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211307, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211307, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211308 q = 1) (hb : d245259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211308, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211308, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79744 (p : Pattern) (ha : d211314 p = 1) (hb : d245265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211292 q = 1) (hb : d244637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211292, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79740 q ha hb
    | true =>
      simp only [d211292, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79741 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211293 q = 1) (hb : d244638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211293, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211293, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211294 q = 1) (hb : d245246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211294, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211294, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211295 q = 1) (hb : d245247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211295, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211295, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211299 q = 1) (hb : d245249 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211299, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211299, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79742 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24538 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211300 q = 1) (hb : d245250 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211300, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211300, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211301 q = 1) (hb : d245251 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211301, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211301, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211302 q = 1) (hb : d245252 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211302, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211302, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211303 q = 1) (hb : d245253 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211303, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211303, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211309 q = 1) (hb : d245260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211309, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211309, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79743 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24674 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211310 q = 1) (hb : d245261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211310, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211310, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211311 q = 1) (hb : d245262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211311, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211311, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211312 q = 1) (hb : d245263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211312, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211312, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211313 q = 1) (hb : d245264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211313, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211313, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211314 q = 1) (hb : d245265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211314, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211314, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79745 (p : Pattern) (ha : d211320 p = 1) (hb : d245271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211315 q = 1) (hb : d245266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211315, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211315, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79744 q ha hb
  have h2 (q : Pattern) (ha : d211316 q = 1) (hb : d245267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211316, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211316, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211317 q = 1) (hb : d245268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211317, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211317, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211318 q = 1) (hb : d245269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211318, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211318, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211319 q = 1) (hb : d245270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211319, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211319, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211320 q = 1) (hb : d245271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211320, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211320, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79746 (p : Pattern) (ha : d211329 p = 1) (hb : d244879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211325 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211325, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211325, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211326 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211326, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211326, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211327 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211327, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211327, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211328 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211328, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211328, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211329 q = 1) (hb : d244879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211329, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211329, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79747 (p : Pattern) (ha : d211334 p = 1) (hb : d244889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211325 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211325, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211325, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211326 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211326, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211326, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211327 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211327, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211327, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211328 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211328, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211328, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24874 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211330 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211330, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211330, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211331 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211331, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211331, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211332 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211332, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211332, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211333 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211333, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211333, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211334 q = 1) (hb : d244889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211334, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211334, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79748 (p : Pattern) (ha : d211341 p = 1) (hb : d245278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211330 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211330, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211330, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211331 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211331, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211331, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211339 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211339, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211339, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211340 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211340, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211340, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211341 q = 1) (hb : d245278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211341, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211341, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79749 (p : Pattern) (ha : d211351 p = 1) (hb : d245289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211347 q = 1) (hb : d245285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211347, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211347, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211348 q = 1) (hb : d245286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211348, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211348, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211349 q = 1) (hb : d245287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211349, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211349, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211350 q = 1) (hb : d245288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211350, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211350, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211351 q = 1) (hb : d245289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211351, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211351, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
