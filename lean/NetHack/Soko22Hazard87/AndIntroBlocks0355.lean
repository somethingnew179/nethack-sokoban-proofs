import NetHack.Soko22Hazard87.AndIntroBlocks0354
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro88750 (p : Pattern) (ha : d319428 p = 1) (hb : d325973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319140 q = 1) (hb : d325701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319140, d325701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319140, d325701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88678 q ha hb
  have h2 (q : Pattern) (ha : d319049 q = 1) (hb : d325610 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319049, d325610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88678 q ha hb
    | true =>
      simp only [d319049, d325610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319141 q = 1) (hb : d325702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319141, d325702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319141, d325702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319050 q = 1) (hb : d325611 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319050, d325611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319050, d325611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319142 q = 1) (hb : d325703 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319142, d325703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319142, d325703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319143 q = 1) (hb : d325704 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319143, d325704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319143, d325704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319418 q = 1) (hb : d325963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319418, d325963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319418, d325963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88709 q ha hb
  have h8 (q : Pattern) (ha : d319213 q = 1) (hb : d325773 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319213, d325773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88709 q ha hb
    | true =>
      simp only [d319213, d325773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319419 q = 1) (hb : d325964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319419, d325964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319419, d325964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319214 q = 1) (hb : d325774 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319214, d325774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319214, d325774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319420 q = 1) (hb : d325965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319420, d325965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319420, d325965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319421 q = 1) (hb : d325966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319421, d325966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319421, d325966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319422 q = 1) (hb : d325967 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319422, d325967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319422, d325967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319427 q = 1) (hb : d325972 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319427, d325972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319427, d325972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319428 q = 1) (hb : d325973 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319428, d325973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319428, d325973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88751 (p : Pattern) (ha : d319434 p = 1) (hb : d325979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318921 q = 1) (hb : d325494 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d318921, d325494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318921, d325494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88641 q ha hb
  have h2 (q : Pattern) (ha : d318850 q = 1) (hb : d325423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d318850, d325423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88641 q ha hb
    | true =>
      simp only [d318850, d325423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d318922 q = 1) (hb : d325495 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d318922, d325495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318922, d325495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d318851 q = 1) (hb : d325424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d318851, d325424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318851, d325424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d318923 q = 1) (hb : d325496 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d318923, d325496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318923, d325496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318924 q = 1) (hb : d325497 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d318924, d325497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318924, d325497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319418 q = 1) (hb : d325963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319418, d325963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319418, d325963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88709 q ha hb
  have h8 (q : Pattern) (ha : d319213 q = 1) (hb : d325773 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319213, d325773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88709 q ha hb
    | true =>
      simp only [d319213, d325773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319419 q = 1) (hb : d325964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319419, d325964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319419, d325964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319214 q = 1) (hb : d325774 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319214, d325774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319214, d325774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319420 q = 1) (hb : d325965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319420, d325965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319420, d325965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319421 q = 1) (hb : d325966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319421, d325966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319421, d325966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319433 q = 1) (hb : d325978 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319433, d325978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319433, d325978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319427 q = 1) (hb : d325972 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319427, d325972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319427, d325972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319434 q = 1) (hb : d325979 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319434, d325979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319434, d325979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88752 (p : Pattern) (ha : d319438 p = 1) (hb : d325983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319418 q = 1) (hb : d325963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319418, d325963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319418, d325963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88709 q ha hb
  have h2 (q : Pattern) (ha : d319213 q = 1) (hb : d325773 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319213, d325773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88709 q ha hb
    | true =>
      simp only [d319213, d325773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319419 q = 1) (hb : d325964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319419, d325964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319419, d325964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319214 q = 1) (hb : d325774 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319214, d325774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319214, d325774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319420 q = 1) (hb : d325965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319420, d325965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319420, d325965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319421 q = 1) (hb : d325966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319421, d325966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319421, d325966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319427 q = 1) (hb : d325972 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319427, d325972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319427, d325972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319438 q = 1) (hb : d325983 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319438, d325983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319438, d325983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88753 (p : Pattern) (ha : d319444 p = 1) (hb : d325989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319424 q = 1) (hb : d325969 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319424, d325969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88748 q ha hb
    | true =>
      simp only [d319424, d325969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88749 q ha hb
  have h2 (q : Pattern) (ha : d319425 q = 1) (hb : d325970 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319425, d325970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319425, d325970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319426 q = 1) (hb : d325971 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319426, d325971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319426, d325971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319429 q = 1) (hb : d325974 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319429, d325974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88749 q ha hb
    | true =>
      simp only [d319429, d325974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88750 q ha hb
  have h5 (q : Pattern) (ha : d319430 q = 1) (hb : d325975 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319430, d325975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319430, d325975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319431 q = 1) (hb : d325976 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319431, d325976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319431, d325976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319432 q = 1) (hb : d325977 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319432, d325977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319432, d325977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319435 q = 1) (hb : d325980 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319435, d325980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88749 q ha hb
    | true =>
      simp only [d319435, d325980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88751 q ha hb
  have h9 (q : Pattern) (ha : d319436 q = 1) (hb : d325981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319436, d325981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319436, d325981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319437 q = 1) (hb : d325982 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319437, d325982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319437, d325982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319439 q = 1) (hb : d325984 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319439, d325984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88751 q ha hb
    | true =>
      simp only [d319439, d325984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88752 q ha hb
  have h12 (q : Pattern) (ha : d319440 q = 1) (hb : d325985 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319440, d325985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319440, d325985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319441 q = 1) (hb : d325986 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319441, d325986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319441, d325986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319442 q = 1) (hb : d325987 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319442, d325987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319442, d325987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319443 q = 1) (hb : d325988 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319443, d325988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319443, d325988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319444 q = 1) (hb : d325989 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319444, d325989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319444, d325989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro88754 (p : Pattern) (ha : d319449 p = 1) (hb : d325994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319435 q = 1) (hb : d325980 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319435, d325980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88749 q ha hb
    | true =>
      simp only [d319435, d325980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88751 q ha hb
  have h2 (q : Pattern) (ha : d319436 q = 1) (hb : d325981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319436, d325981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319436, d325981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319437 q = 1) (hb : d325982 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319437, d325982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319437, d325982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319439 q = 1) (hb : d325984 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319439, d325984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88751 q ha hb
    | true =>
      simp only [d319439, d325984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88752 q ha hb
  have h5 (q : Pattern) (ha : d319440 q = 1) (hb : d325985 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319440, d325985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319440, d325985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319441 q = 1) (hb : d325986 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319441, d325986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319441, d325986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319442 q = 1) (hb : d325987 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319442, d325987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319442, d325987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319447 q = 1) (hb : d325992 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319447, d325992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319447, d325992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319448 q = 1) (hb : d325993 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319448, d325993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319448, d325993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319449 q = 1) (hb : d325994 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319449, d325994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319449, d325994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro88755 (p : Pattern) (ha : d319455 p = 1) (hb : d326000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319445 q = 1) (hb : d325990 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319445, d325990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88753 q ha hb
    | true =>
      simp only [d319445, d325990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319446 q = 1) (hb : d325991 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319446, d325991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319446, d325991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319450 q = 1) (hb : d325995 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319450, d325995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88754 q ha hb
    | true =>
      simp only [d319450, d325995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319451 q = 1) (hb : d325996 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319451, d325996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319451, d325996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319452 q = 1) (hb : d325997 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319452, d325997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319452, d325997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319453 q = 1) (hb : d325998 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319453, d325998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319453, d325998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319454 q = 1) (hb : d325999 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319454, d325999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319454, d325999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319455 q = 1) (hb : d326000 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319455, d326000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319455, d326000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88756 (p : Pattern) (ha : d319457 p = 1) (hb : d326002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319439 q = 1) (hb : d325984 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319439, d325984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88751 q ha hb
    | true =>
      simp only [d319439, d325984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88752 q ha hb
  have h2 (q : Pattern) (ha : d319440 q = 1) (hb : d325985 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319440, d325985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319440, d325985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319441 q = 1) (hb : d325986 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319441, d325986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319441, d325986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319447 q = 1) (hb : d325992 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319447, d325992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319447, d325992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319456 q = 1) (hb : d326001 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319456, d326001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319456, d326001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319457 q = 1) (hb : d326002 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319457, d326002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319457, d326002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88757 (p : Pattern) (ha : d319463 p = 1) (hb : d326008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319450 q = 1) (hb : d325995 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319450, d325995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88754 q ha hb
    | true =>
      simp only [d319450, d325995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319451 q = 1) (hb : d325996 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319451, d325996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319451, d325996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319458 q = 1) (hb : d326003 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319458, d326003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88756 q ha hb
    | true =>
      simp only [d319458, d326003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319459 q = 1) (hb : d326004 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319459, d326004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319459, d326004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319460 q = 1) (hb : d326005 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319460, d326005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319460, d326005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319461 q = 1) (hb : d326006 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319461, d326006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319461, d326006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319462 q = 1) (hb : d326007 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319462, d326007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319462, d326007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319463 q = 1) (hb : d326008 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319463, d326008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319463, d326008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88758 (p : Pattern) (ha : d319474 p = 1) (hb : d326014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319450 q = 1) (hb : d325995 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319450, d325995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88754 q ha hb
    | true =>
      simp only [d319450, d325995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319451 q = 1) (hb : d325996 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319451, d325996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319451, d325996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319471 q = 1) (hb : d326011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319471, d326011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319471, d326011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319472 q = 1) (hb : d326012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319472, d326012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319472, d326012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319473 q = 1) (hb : d326013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319473, d326013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319473, d326013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319474 q = 1) (hb : d326014 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319474, d326014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319474, d326014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88759 (p : Pattern) (ha : d319480 p = 1) (hb : d326020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319464 q = 1) (hb : d326009 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319464, d326009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88755 q ha hb
    | true =>
      simp only [d319464, d326009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88757 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319470 q = 1) (hb : d326010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319470, d326010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319470, d326010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319475 q = 1) (hb : d326015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319475, d326015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88758 q ha hb
    | true =>
      simp only [d319475, d326015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319476 q = 1) (hb : d326016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319476, d326016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319476, d326016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319477 q = 1) (hb : d326017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319477, d326017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319477, d326017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319478 q = 1) (hb : d326018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319478, d326018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319478, d326018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319479 q = 1) (hb : d326019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319479, d326019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319479, d326019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319480 q = 1) (hb : d326020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319480, d326020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319480, d326020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro88760 (p : Pattern) (ha : d319468 p = 1) (hb : d326025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319458 q = 1) (hb : d326003 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319458, d326003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88756 q ha hb
    | true =>
      simp only [d319458, d326003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319459 q = 1) (hb : d326004 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319459, d326004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319459, d326004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319465 q = 1) (hb : d326022 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319465, d326022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319465, d326022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319466 q = 1) (hb : d326023 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319466, d326023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319466, d326023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319467 q = 1) (hb : d326024 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319467, d326024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319467, d326024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319468 q = 1) (hb : d326025 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319468, d326025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319468, d326025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88761 (p : Pattern) (ha : d319487 p = 1) (hb : d326031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319482 q = 1) (hb : d326026 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319482, d326026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88760 q ha hb
    | true =>
      simp only [d319482, d326026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319483 q = 1) (hb : d326027 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319483, d326027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319483, d326027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319484 q = 1) (hb : d326028 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319484, d326028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319484, d326028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319485 q = 1) (hb : d326029 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319485, d326029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319485, d326029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319486 q = 1) (hb : d326030 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319486, d326030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319486, d326030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319487 q = 1) (hb : d326031 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319487, d326031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319487, d326031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88762 (p : Pattern) (ha : d319493 p = 1) (hb : d326037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319253 q = 1) (hb : d325813 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319253, d325813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319253, d325813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88717 q ha hb
  have h2 (q : Pattern) (ha : d319254 q = 1) (hb : d325814 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319254, d325814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319254, d325814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319263 q = 1) (hb : d325823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319263, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88717 q ha hb
    | true =>
      simp only [d319263, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88720 q ha hb
  have h4 (q : Pattern) (ha : d319264 q = 1) (hb : d325824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319264, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319264, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319265 q = 1) (hb : d325825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319265, d325825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319265, d325825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319376 q = 1) (hb : d325921 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319376, d325921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88736 q ha hb
    | true =>
      simp only [d319376, d325921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88743 q ha hb
  have h7 (q : Pattern) (ha : d319389 q = 1) (hb : d325934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319389, d325934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88744 q ha hb
    | true =>
      simp only [d319389, d325934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88745 q ha hb
  have h8 (q : Pattern) (ha : d319390 q = 1) (hb : d325935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319390, d325935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319390, d325935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319391 q = 1) (hb : d325936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319391, d325936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319391, d325936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d319392 q = 1) (hb : d325937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319392, d325937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319392, d325937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319396 q = 1) (hb : d325941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319396, d325941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319396, d325941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88746 q ha hb
  have h12 (q : Pattern) (ha : d319398 q = 1) (hb : d325943 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319398, d325943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319398, d325943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88747 q ha hb
  have h13 (q : Pattern) (ha : d319399 q = 1) (hb : d325944 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319399, d325944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319399, d325944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319400 q = 1) (hb : d325945 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319400, d325945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319400, d325945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319401 q = 1) (hb : d325946 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319401, d325946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319401, d325946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319402 q = 1) (hb : d325947 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319402, d325947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319402, d325947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319481 q = 1) (hb : d326021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319481, d326021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319481, d326021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88759 q ha hb
  have h18 (q : Pattern) (ha : d319488 q = 1) (hb : d326032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319488, d326032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319488, d326032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88761 q ha hb
  have h19 (q : Pattern) (ha : d319489 q = 1) (hb : d326033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319489, d326033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319489, d326033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d319490 q = 1) (hb : d326034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319490, d326034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319490, d326034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d319491 q = 1) (hb : d326035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319491, d326035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319491, d326035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319492 q = 1) (hb : d326036 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319492, d326036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319492, d326036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d319493 q = 1) (hb : d326037 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319493, d326037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319493, d326037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro88763 (p : Pattern) (ha : d319499 p = 1) (hb : d326043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319494 q = 1) (hb : d326038 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319494, d326038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319494, d326038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88762 q ha hb
  have h2 (q : Pattern) (ha : d319495 q = 1) (hb : d326039 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319495, d326039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319495, d326039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319496 q = 1) (hb : d326040 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319496, d326040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319496, d326040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319497 q = 1) (hb : d326041 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319497, d326041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319497, d326041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319498 q = 1) (hb : d326042 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319498, d326042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319498, d326042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319499 q = 1) (hb : d326043 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319499, d326043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319499, d326043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88764 (p : Pattern) (ha : d319512 p = 1) (hb : d326056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h2 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319504 q = 1) (hb : d326048 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319504, d326048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319504, d326048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319505 q = 1) (hb : d326049 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319505, d326049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319505, d326049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319506 q = 1) (hb : d326050 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319506, d326050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319506, d326050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319507 q = 1) (hb : d326051 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88640 q hb ha
    | true =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q hb ha
  have h12 (q : Pattern) (ha : d319508 q = 1) (hb : d326052 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319509 q = 1) (hb : d326053 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319509, d326053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319509, d326053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319294 q = 1) (hb : d325419 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319294, d325419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319294, d325419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319510 q = 1) (hb : d326054 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319510, d326054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319510, d326054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319511 q = 1) (hb : d326055 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319511, d326055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319511, d326055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d319512 q = 1) (hb : d326056 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319512, d326056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319512, d326056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88765 (p : Pattern) (ha : d319524 p = 1) (hb : d326066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319507 q = 1) (hb : d326051 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88640 q hb ha
    | true =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q hb ha
  have h4 (q : Pattern) (ha : d319508 q = 1) (hb : d326052 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319509 q = 1) (hb : d326053 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319509, d326053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319509, d326053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319030 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88675 q ha hb
    | true =>
      simp only [d45574, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319031 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d319032 q = 1) (hb : d325419 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319032, d325419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319032, d325419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319517 q = 1) (hb : d326054 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319517, d326054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319517, d326054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319518 q = 1) (hb : d326055 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319518, d326055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319518, d326055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d319519 q = 1) (hb : d326061 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319519, d326061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88728 q ha hb
    | true =>
      simp only [d319519, d326061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q hb ha
  have h14 (q : Pattern) (ha : d319520 q = 1) (hb : d326062 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319520, d326062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319520, d326062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d319521 q = 1) (hb : d326063 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319521, d326063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319521, d326063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d319522 q = 1) (hb : d326064 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319522, d326064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319522, d326064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d319523 q = 1) (hb : d326065 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319523, d326065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319523, d326065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h18 (q : Pattern) (ha : d319524 q = 1) (hb : d326066 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319524, d326066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319524, d326066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88766 (p : Pattern) (ha : d319533 p = 1) (hb : d326075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319306 q = 1) (hb : d325851 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319306, d325851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88728 q ha hb
    | true =>
      simp only [d319306, d325851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d319307 q = 1) (hb : d325852 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319307, d325852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319307, d325852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319530 q = 1) (hb : d326072 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319530, d326072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319530, d326072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319531 q = 1) (hb : d326073 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319531, d326073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319531, d326073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d319532 q = 1) (hb : d326074 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319532, d326074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319532, d326074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d319519 q = 1) (hb : d326061 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319519, d326061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88728 q ha hb
    | true =>
      simp only [d319519, d326061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q hb ha
  have h9 (q : Pattern) (ha : d319520 q = 1) (hb : d326062 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319520, d326062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319520, d326062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d319521 q = 1) (hb : d326063 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319521, d326063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319521, d326063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319522 q = 1) (hb : d326064 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319522, d326064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319522, d326064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d319523 q = 1) (hb : d326065 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319523, d326065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319523, d326065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d319533 q = 1) (hb : d326075 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319533, d326075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319533, d326075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88767 (p : Pattern) (ha : d319542 p = 1) (hb : d326084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319507 q = 1) (hb : d326051 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88640 q hb ha
    | true =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319508 q = 1) (hb : d326052 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319538 q = 1) (hb : d326080 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319538, d326080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319538, d326080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319539 q = 1) (hb : d326081 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319539, d326081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319539, d326081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d319540 q = 1) (hb : d326082 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319540, d326082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319540, d326082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319541 q = 1) (hb : d326083 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319541, d326083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319541, d326083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h10 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1118 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1119 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d319542 q = 1) (hb : d326084 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319542, d326084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319542, d326084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro88768 (p : Pattern) (ha : d319548 p = 1) (hb : d326090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319513 q = 1) (hb : d326057 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319513, d326057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88764 q ha hb
    | true =>
      simp only [d319513, d326057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319514 q = 1) (hb : d326058 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319514, d326058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319514, d326058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319515 q = 1) (hb : d326059 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319515, d326059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319515, d326059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319516 q = 1) (hb : d326060 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319516, d326060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319516, d326060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319525 q = 1) (hb : d326067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319525, d326067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88765 q ha hb
    | true =>
      simp only [d319525, d326067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319526 q = 1) (hb : d326068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319526, d326068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319526, d326068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319527 q = 1) (hb : d326069 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319527, d326069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319527, d326069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319528 q = 1) (hb : d326070 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319528, d326070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319528, d326070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319529 q = 1) (hb : d326071 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319529, d326071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319529, d326071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319534 q = 1) (hb : d326076 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88766 q ha hb
    | true =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319535 q = 1) (hb : d326077 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319536 q = 1) (hb : d326078 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319536, d326078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319536, d326078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319537 q = 1) (hb : d326079 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319537, d326079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319537, d326079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d319543 q = 1) (hb : d326085 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
    | true =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319544 q = 1) (hb : d326086 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319545 q = 1) (hb : d326087 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319545, d326087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319545, d326087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319546 q = 1) (hb : d326088 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319546, d326088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319546, d326088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d319547 q = 1) (hb : d326089 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319547, d326089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319547, d326089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d319548 q = 1) (hb : d326090 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319548, d326090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319548, d326090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88769 (p : Pattern) (ha : d319554 p = 1) (hb : d326096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319507 q = 1) (hb : d326051 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88640 q hb ha
    | true =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q hb ha
  have h4 (q : Pattern) (ha : d319508 q = 1) (hb : d326052 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319509 q = 1) (hb : d326053 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319509, d326053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319509, d326053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319030 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88675 q ha hb
    | true =>
      simp only [d45574, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319031 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d319032 q = 1) (hb : d325419 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319032, d325419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319032, d325419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319517 q = 1) (hb : d326054 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319517, d326054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319517, d326054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319518 q = 1) (hb : d326055 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319518, d326055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319518, d326055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d319549 q = 1) (hb : d326091 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319549, d326091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d319549, d326091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q hb ha
  have h14 (q : Pattern) (ha : d319550 q = 1) (hb : d326092 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319550, d326092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319550, d326092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d319551 q = 1) (hb : d326093 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319551, d326093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319551, d326093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d318732 q = 1) (hb : d325310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d318732, d325310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318732, d325310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d319552 q = 1) (hb : d326094 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319552, d326094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319552, d326094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d319553 q = 1) (hb : d326095 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319553, d326095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319553, d326095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d319554 q = 1) (hb : d326096 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319554, d326096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319554, d326096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro88770 (p : Pattern) (ha : d319559 p = 1) (hb : d326101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319507 q = 1) (hb : d326051 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88640 q hb ha
    | true =>
      simp only [d319507, d326051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319508 q = 1) (hb : d326052 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319508, d326052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319549 q = 1) (hb : d326091 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319549, d326091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d319549, d326091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q hb ha
  have h4 (q : Pattern) (ha : d319550 q = 1) (hb : d326092 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319550, d326092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319550, d326092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319551 q = 1) (hb : d326093 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319551, d326093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319551, d326093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d318732 q = 1) (hb : d325310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d318732, d325310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318732, d325310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d319552 q = 1) (hb : d326094 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319552, d326094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319552, d326094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319553 q = 1) (hb : d326095 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319553, d326095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319553, d326095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h14 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1118 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1119 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d319559 q = 1) (hb : d326101 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319559, d326101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319559, d326101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro88771 (p : Pattern) (ha : d319566 p = 1) (hb : d326108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319555 q = 1) (hb : d326097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319555, d326097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88769 q ha hb
    | true =>
      simp only [d319555, d326097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319556 q = 1) (hb : d326098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319556, d326098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319556, d326098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319557 q = 1) (hb : d326099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319557, d326099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319557, d326099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319558 q = 1) (hb : d326100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319558, d326100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319558, d326100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319560 q = 1) (hb : d326102 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
    | true =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319561 q = 1) (hb : d326103 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319562 q = 1) (hb : d326104 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319562, d326104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319562, d326104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319563 q = 1) (hb : d326105 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319563, d326105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319563, d326105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319564 q = 1) (hb : d326106 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319564, d326106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319564, d326106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319543 q = 1) (hb : d326085 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
    | true =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319544 q = 1) (hb : d326086 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319545 q = 1) (hb : d326087 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319545, d326087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319545, d326087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319546 q = 1) (hb : d326088 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319546, d326088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319546, d326088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d319565 q = 1) (hb : d326107 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319565, d326107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319565, d326107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319566 q = 1) (hb : d326108 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319566, d326108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319566, d326108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88772 (p : Pattern) (ha : d319571 p = 1) (hb : d326113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319560 q = 1) (hb : d326102 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
    | true =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319561 q = 1) (hb : d326103 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319562 q = 1) (hb : d326104 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319562, d326104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319562, d326104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319563 q = 1) (hb : d326105 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319563, d326105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319563, d326105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319570 q = 1) (hb : d326112 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319570, d326112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319570, d326112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d122941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d319571 q = 1) (hb : d326113 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319571, d326113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319571, d326113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro88773 (p : Pattern) (ha : d319578 p = 1) (hb : d326120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319567 q = 1) (hb : d326109 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319567, d326109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88768 q ha hb
    | true =>
      simp only [d319567, d326109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
  have h2 (q : Pattern) (ha : d319568 q = 1) (hb : d326110 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319568, d326110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319568, d326110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319569 q = 1) (hb : d326111 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319569, d326111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319569, d326111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319572 q = 1) (hb : d326114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
    | true =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88772 q ha hb
  have h5 (q : Pattern) (ha : d319573 q = 1) (hb : d326115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319574 q = 1) (hb : d326116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319575 q = 1) (hb : d326117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319575, d326117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319575, d326117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319576 q = 1) (hb : d326118 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319576, d326118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319576, d326118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319577 q = 1) (hb : d326119 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319577, d326119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319577, d326119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319578 q = 1) (hb : d326120 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319578, d326120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319578, d326120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro88774 (p : Pattern) (ha : d319582 p = 1) (hb : d326124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319572 q = 1) (hb : d326114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
    | true =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88772 q ha hb
  have h2 (q : Pattern) (ha : d319573 q = 1) (hb : d326115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319574 q = 1) (hb : d326116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319576 q = 1) (hb : d326118 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319576, d326118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319576, d326118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319581 q = 1) (hb : d326123 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319581, d326123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319581, d326123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319582 q = 1) (hb : d326124 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319582, d326124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319582, d326124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88775 (p : Pattern) (ha : d319588 p = 1) (hb : d326130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319585 q = 1) (hb : d326127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319586 q = 1) (hb : d326128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319587 q = 1) (hb : d326129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319587, d326129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319587, d326129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319588 q = 1) (hb : d326130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319588, d326130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319588, d326130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88776 (p : Pattern) (ha : d319592 p = 1) (hb : d326134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319589 q = 1) (hb : d326131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319590 q = 1) (hb : d326132 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319591 q = 1) (hb : d326133 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319591, d326133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319591, d326133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319592 q = 1) (hb : d326134 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319592, d326134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319592, d326134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88777 (p : Pattern) (ha : d319598 p = 1) (hb : d326140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319593 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
    | true =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
  have h2 (q : Pattern) (ha : d319594 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319594, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319594, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319595 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319595, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319595, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319596 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319596, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319596, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319597 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319597, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319597, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319598 q = 1) (hb : d326140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319598, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319598, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88778 (p : Pattern) (ha : d319601 p = 1) (hb : d326143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319585 q = 1) (hb : d326127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319586 q = 1) (hb : d326128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319587 q = 1) (hb : d326129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319587, d326129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319587, d326129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319601 q = 1) (hb : d326143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319601, d326143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319601, d326143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88779 (p : Pattern) (ha : d319602 p = 1) (hb : d326144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319589 q = 1) (hb : d326131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319590 q = 1) (hb : d326132 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319591 q = 1) (hb : d326133 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319591, d326133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319591, d326133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319602 q = 1) (hb : d326144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319602, d326144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319602, d326144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88780 (p : Pattern) (ha : d319608 p = 1) (hb : d326150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319593 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
    | true =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
  have h2 (q : Pattern) (ha : d319594 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319594, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319594, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319595 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319595, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319595, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319596 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319596, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319596, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319597 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319597, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319597, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319603 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319603, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88778 q ha hb
    | true =>
      simp only [d319603, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88779 q ha hb
  have h7 (q : Pattern) (ha : d319604 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319604, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319604, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319605 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319605, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319605, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319606 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319606, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319606, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319607 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319607, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319607, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319608 q = 1) (hb : d326150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319608, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319608, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88781 (p : Pattern) (ha : d319613 p = 1) (hb : d326155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319585 q = 1) (hb : d326127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319586 q = 1) (hb : d326128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319612 q = 1) (hb : d326154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319612, d326154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319612, d326154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319613 q = 1) (hb : d326155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319613, d326155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319613, d326155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88782 (p : Pattern) (ha : d319615 p = 1) (hb : d326157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319589 q = 1) (hb : d326131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319590 q = 1) (hb : d326132 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319614 q = 1) (hb : d326156 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319614, d326156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319614, d326156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319615 q = 1) (hb : d326157 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319615, d326157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319615, d326157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88783 (p : Pattern) (ha : d319622 p = 1) (hb : d326164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319585 q = 1) (hb : d326127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319620 q = 1) (hb : d326162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319620, d326162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319620, d326162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319621 q = 1) (hb : d326163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319621, d326163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319621, d326163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319622 q = 1) (hb : d326164 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319622, d326164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319622, d326164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88784 (p : Pattern) (ha : d319625 p = 1) (hb : d326167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319589 q = 1) (hb : d326131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319623 q = 1) (hb : d326165 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319623, d326165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319623, d326165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319624 q = 1) (hb : d326166 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319624, d326166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319624, d326166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319625 q = 1) (hb : d326167 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319625, d326167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319625, d326167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88785 (p : Pattern) (ha : d319632 p = 1) (hb : d326171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46032 q = 1) (hb : d319629 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46032, d319629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46032, d319629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46033 q = 1) (hb : d319630 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46033, d319630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46033, d319630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46034 q = 1) (hb : d319631 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46034, d319631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46034, d319631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h7 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319504 q = 1) (hb : d326048 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319504, d326048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319504, d326048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319505 q = 1) (hb : d326049 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319505, d326049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319505, d326049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d319506 q = 1) (hb : d326050 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319506, d326050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319506, d326050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d319632 q = 1) (hb : d326171 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319632, d326171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d319632, d326171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro88786 (p : Pattern) (ha : d319644 p = 1) (hb : d326179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h2 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319504 q = 1) (hb : d326048 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319504, d326048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319504, d326048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319505 q = 1) (hb : d326049 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319505, d326049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319505, d326049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319506 q = 1) (hb : d326050 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319506, d326050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319506, d326050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319640 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d319306 q = 1) (hb : d325851 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319306, d325851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88728 q ha hb
    | true =>
      simp only [d319306, d325851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319307 q = 1) (hb : d325852 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319307, d325852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319307, d325852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d319641 q = 1) (hb : d326176 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319641, d326176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319641, d326176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319642 q = 1) (hb : d326177 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319642, d326177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319642, d326177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319643 q = 1) (hb : d326178 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319643, d326178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319643, d326178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d319644 q = 1) (hb : d326179 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319644, d326179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319644, d326179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro88787 (p : Pattern) (ha : d319653 p = 1) (hb : d326185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319640 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319306 q = 1) (hb : d325851 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319306, d325851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88728 q ha hb
    | true =>
      simp only [d319306, d325851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319307 q = 1) (hb : d325852 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319307, d325852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319307, d325852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d319641 q = 1) (hb : d326176 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319641, d326176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319641, d326176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319642 q = 1) (hb : d326177 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319642, d326177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319642, d326177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d319643 q = 1) (hb : d326178 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319643, d326178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319643, d326178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d319653 q = 1) (hb : d326185 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319653, d326185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319653, d326185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88788 (p : Pattern) (ha : d319659 p = 1) (hb : d326191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319633 q = 1) (hb : d326172 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319633, d326172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88785 q ha hb
    | true =>
      simp only [d319633, d326172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319634 q = 1) (hb : d326173 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319634, d326173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319634, d326173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319635 q = 1) (hb : d326174 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319635, d326174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319635, d326174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319636 q = 1) (hb : d326175 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319636, d326175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319636, d326175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319645 q = 1) (hb : d326180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319645, d326180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88786 q ha hb
    | true =>
      simp only [d319645, d326180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319646 q = 1) (hb : d326181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319646, d326181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319646, d326181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319647 q = 1) (hb : d326182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319647, d326182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319647, d326182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319648 q = 1) (hb : d326183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319648, d326183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319648, d326183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319649 q = 1) (hb : d326184 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319649, d326184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319649, d326184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319654 q = 1) (hb : d326186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319654, d326186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88787 q ha hb
    | true =>
      simp only [d319654, d326186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319655 q = 1) (hb : d326187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319655, d326187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319655, d326187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319656 q = 1) (hb : d326188 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319656, d326188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319656, d326188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319657 q = 1) (hb : d326189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319657, d326189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319657, d326189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d319534 q = 1) (hb : d326076 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88766 q ha hb
    | true =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319535 q = 1) (hb : d326077 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319536 q = 1) (hb : d326078 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319536, d326078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319536, d326078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319537 q = 1) (hb : d326079 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319537, d326079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319537, d326079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d319658 q = 1) (hb : d326190 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319658, d326190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319658, d326190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d319659 q = 1) (hb : d326191 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319659, d326191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319659, d326191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88789 (p : Pattern) (ha : d319666 p = 1) (hb : d326198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319502 q = 1) (hb : d326046 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88674 q hb ha
    | true =>
      simp only [d319502, d326046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319503 q = 1) (hb : d326047 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319503, d326047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319519 q = 1) (hb : d326061 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d319519, d326061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88728 q ha hb
    | true =>
      simp only [d319519, d326061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q hb ha
  have h4 (q : Pattern) (ha : d319520 q = 1) (hb : d326062 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319520, d326062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319520, d326062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319663 q = 1) (hb : d326195 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319663, d326195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319663, d326195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319664 q = 1) (hb : d326196 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319664, d326196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319664, d326196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d319665 q = 1) (hb : d326197 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319665, d326197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319665, d326197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d318730 q = 1) (hb : d325308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88622 q ha hb
    | true =>
      simp only [d318730, d325308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d318731 q = 1) (hb : d325309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318731, d325309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d319521 q = 1) (hb : d326063 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319521, d326063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319521, d326063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319522 q = 1) (hb : d326064 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319522, d326064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319522, d326064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d319523 q = 1) (hb : d326065 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319523, d326065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319523, d326065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d319666 q = 1) (hb : d326198 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319666, d326198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319666, d326198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro88790 (p : Pattern) (ha : d319672 p = 1) (hb : d326204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319667 q = 1) (hb : d326199 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319667, d326199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88789 q ha hb
    | true =>
      simp only [d319667, d326199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319668 q = 1) (hb : d326200 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319668, d326200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319668, d326200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319669 q = 1) (hb : d326201 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319669, d326201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319669, d326201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319670 q = 1) (hb : d326202 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319670, d326202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319670, d326202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319543 q = 1) (hb : d326085 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
    | true =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319544 q = 1) (hb : d326086 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319545 q = 1) (hb : d326087 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319545, d326087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319545, d326087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319546 q = 1) (hb : d326088 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319546, d326088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319546, d326088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319671 q = 1) (hb : d326203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319671, d326203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319671, d326203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319565 q = 1) (hb : d326107 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319565, d326107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319565, d326107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319672 q = 1) (hb : d326204 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319672, d326204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319672, d326204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88791 (p : Pattern) (ha : d319678 p = 1) (hb : d326210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319660 q = 1) (hb : d326192 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319660, d326192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88788 q ha hb
    | true =>
      simp only [d319660, d326192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88768 q ha hb
  have h2 (q : Pattern) (ha : d319661 q = 1) (hb : d326193 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319661, d326193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319661, d326193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319662 q = 1) (hb : d326194 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319662, d326194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319662, d326194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319673 q = 1) (hb : d326205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319673, d326205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88768 q ha hb
    | true =>
      simp only [d319673, d326205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88790 q ha hb
  have h5 (q : Pattern) (ha : d319674 q = 1) (hb : d326206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319674, d326206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319674, d326206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319675 q = 1) (hb : d326207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319675, d326207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319675, d326207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319676 q = 1) (hb : d326208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319676, d326208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319676, d326208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319567 q = 1) (hb : d326109 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319567, d326109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88768 q ha hb
    | true =>
      simp only [d319567, d326109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
  have h9 (q : Pattern) (ha : d319568 q = 1) (hb : d326110 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319568, d326110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319568, d326110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319569 q = 1) (hb : d326111 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319569, d326111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319569, d326111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319572 q = 1) (hb : d326114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
    | true =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88772 q ha hb
  have h12 (q : Pattern) (ha : d319573 q = 1) (hb : d326115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319574 q = 1) (hb : d326116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319575 q = 1) (hb : d326117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319575, d326117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319575, d326117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319677 q = 1) (hb : d326209 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319677, d326209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319677, d326209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319678 q = 1) (hb : d326210 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319678, d326210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319678, d326210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro88792 (p : Pattern) (ha : d319684 p = 1) (hb : d326216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319679 q = 1) (hb : d326211 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319679, d326211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88791 q ha hb
    | true =>
      simp only [d319679, d326211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319680 q = 1) (hb : d326212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319680, d326212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319680, d326212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319681 q = 1) (hb : d326213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319681, d326213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319681, d326213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319682 q = 1) (hb : d326214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319682, d326214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319682, d326214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319683 q = 1) (hb : d326215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319683, d326215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319683, d326215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319684 q = 1) (hb : d326216 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319684, d326216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319684, d326216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88793 (p : Pattern) (ha : d319687 p = 1) (hb : d326219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319560 q = 1) (hb : d326102 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
    | true =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319561 q = 1) (hb : d326103 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319562 q = 1) (hb : d326104 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319562, d326104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319562, d326104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319563 q = 1) (hb : d326105 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319563, d326105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319563, d326105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319570 q = 1) (hb : d326112 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319570, d326112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319570, d326112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319687 q = 1) (hb : d326219 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319687, d326219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319687, d326219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88794 (p : Pattern) (ha : d319693 p = 1) (hb : d326225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319567 q = 1) (hb : d326109 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319567, d326109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88768 q ha hb
    | true =>
      simp only [d319567, d326109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
  have h2 (q : Pattern) (ha : d319568 q = 1) (hb : d326110 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319568, d326110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319568, d326110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319569 q = 1) (hb : d326111 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319569, d326111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319569, d326111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319572 q = 1) (hb : d326114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
    | true =>
      simp only [d319572, d326114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88772 q ha hb
  have h5 (q : Pattern) (ha : d319573 q = 1) (hb : d326115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319573, d326115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319574 q = 1) (hb : d326116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319574, d326116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319575 q = 1) (hb : d326117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319575, d326117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319575, d326117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319688 q = 1) (hb : d326220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319688, d326220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88771 q ha hb
    | true =>
      simp only [d319688, d326220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88793 q ha hb
  have h9 (q : Pattern) (ha : d319689 q = 1) (hb : d326221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319689, d326221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319689, d326221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319690 q = 1) (hb : d326222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319690, d326222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319690, d326222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319691 q = 1) (hb : d326223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319691, d326223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319691, d326223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319692 q = 1) (hb : d326224 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319692, d326224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319692, d326224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319693 q = 1) (hb : d326225 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319693, d326225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319693, d326225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro88795 (p : Pattern) (ha : d319699 p = 1) (hb : d326231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319694 q = 1) (hb : d326226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319694, d326226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88794 q ha hb
    | true =>
      simp only [d319694, d326226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319695 q = 1) (hb : d326227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319695, d326227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319695, d326227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319696 q = 1) (hb : d326228 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319696, d326228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319696, d326228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319697 q = 1) (hb : d326229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319697, d326229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319697, d326229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319698 q = 1) (hb : d326230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319698, d326230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319698, d326230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319699 q = 1) (hb : d326231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319699, d326231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319699, d326231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88796 (p : Pattern) (ha : d319705 p = 1) (hb : d326237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319616 q = 1) (hb : d326158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319616, d326158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88781 q ha hb
    | true =>
      simp only [d319616, d326158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88782 q ha hb
  have h2 (q : Pattern) (ha : d319617 q = 1) (hb : d326159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319617, d326159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319617, d326159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319618 q = 1) (hb : d326160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319618, d326160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319618, d326160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319619 q = 1) (hb : d326161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319619, d326161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319619, d326161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319626 q = 1) (hb : d326168 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319626, d326168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88783 q ha hb
    | true =>
      simp only [d319626, d326168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88784 q ha hb
  have h6 (q : Pattern) (ha : d319627 q = 1) (hb : d326169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319627, d326169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319627, d326169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319628 q = 1) (hb : d326170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319628, d326170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319628, d326170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319685 q = 1) (hb : d326217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319685, d326217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88792 q ha hb
    | true =>
      simp only [d319685, d326217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319686 q = 1) (hb : d326218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d326218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319686, d326218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d319700 q = 1) (hb : d326232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319700, d326232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88795 q ha hb
    | true =>
      simp only [d319700, d326232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319701 q = 1) (hb : d326233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319701, d326233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319701, d326233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319702 q = 1) (hb : d326234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d326234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319702, d326234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319703 q = 1) (hb : d326235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d326235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319703, d326235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319704 q = 1) (hb : d326236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d326236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319704, d326236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319705 q = 1) (hb : d326237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319705, d326237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319705, d326237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro88797 (p : Pattern) (ha : d319706 p = 1) (hb : d326238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319585 q = 1) (hb : d326127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319586 q = 1) (hb : d326128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319586, d326128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319612 q = 1) (hb : d326154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319612, d326154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319612, d326154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319706 q = 1) (hb : d326238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319706, d326238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319706, d326238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88798 (p : Pattern) (ha : d319707 p = 1) (hb : d326239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319589 q = 1) (hb : d326131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319590 q = 1) (hb : d326132 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319590, d326132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319614 q = 1) (hb : d326156 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319614, d326156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319614, d326156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319707 q = 1) (hb : d326239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319707, d326239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319707, d326239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88799 (p : Pattern) (ha : d319712 p = 1) (hb : d326244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319585 q = 1) (hb : d326127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319585, d326127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319620 q = 1) (hb : d326162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319620, d326162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319620, d326162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319621 q = 1) (hb : d326163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319621, d326163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319621, d326163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319712 q = 1) (hb : d326244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319712, d326244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319712, d326244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88800 (p : Pattern) (ha : d319713 p = 1) (hb : d326245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319583 q = 1) (hb : d326125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88774 q ha hb
    | true =>
      simp only [d319583, d326125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319584 q = 1) (hb : d326126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319584, d326126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319589 q = 1) (hb : d326131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319589, d326131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319623 q = 1) (hb : d326165 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319623, d326165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319623, d326165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319624 q = 1) (hb : d326166 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319624, d326166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319624, d326166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319713 q = 1) (hb : d326245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319713, d326245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319713, d326245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88801 (p : Pattern) (ha : d319717 p = 1) (hb : d326249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319679 q = 1) (hb : d326211 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319679, d326211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88791 q ha hb
    | true =>
      simp only [d319679, d326211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319680 q = 1) (hb : d326212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319680, d326212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319680, d326212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319579 q = 1) (hb : d326121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88773 q ha hb
    | true =>
      simp only [d319579, d326121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319580 q = 1) (hb : d326122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319580, d326122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319681 q = 1) (hb : d326213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319681, d326213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319681, d326213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319682 q = 1) (hb : d326214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319682, d326214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319682, d326214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319683 q = 1) (hb : d326215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319683, d326215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319683, d326215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319717 q = 1) (hb : d326249 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319717, d326249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319717, d326249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88802 (p : Pattern) (ha : d319720 p = 1) (hb : d326252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319694 q = 1) (hb : d326226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319694, d326226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88794 q ha hb
    | true =>
      simp only [d319694, d326226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319695 q = 1) (hb : d326227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319695, d326227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319695, d326227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319696 q = 1) (hb : d326228 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319696, d326228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319696, d326228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319697 q = 1) (hb : d326229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319697, d326229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319697, d326229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319698 q = 1) (hb : d326230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319698, d326230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319698, d326230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319720 q = 1) (hb : d326252 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319720, d326252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319720, d326252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88803 (p : Pattern) (ha : d319726 p = 1) (hb : d326258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319616 q = 1) (hb : d326158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319616, d326158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88781 q ha hb
    | true =>
      simp only [d319616, d326158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88782 q ha hb
  have h2 (q : Pattern) (ha : d319617 q = 1) (hb : d326159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319617, d326159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319617, d326159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319618 q = 1) (hb : d326160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319618, d326160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319618, d326160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319619 q = 1) (hb : d326161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319619, d326161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319619, d326161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319626 q = 1) (hb : d326168 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319626, d326168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88783 q ha hb
    | true =>
      simp only [d319626, d326168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88784 q ha hb
  have h6 (q : Pattern) (ha : d319627 q = 1) (hb : d326169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319627, d326169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319627, d326169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319628 q = 1) (hb : d326170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319628, d326170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319628, d326170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319685 q = 1) (hb : d326217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319685, d326217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88792 q ha hb
    | true =>
      simp only [d319685, d326217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319686 q = 1) (hb : d326218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d326218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319686, d326218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d319700 q = 1) (hb : d326232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319700, d326232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88795 q ha hb
    | true =>
      simp only [d319700, d326232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319701 q = 1) (hb : d326233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319701, d326233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319701, d326233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319702 q = 1) (hb : d326234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d326234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319702, d326234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319703 q = 1) (hb : d326235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d326235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319703, d326235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319704 q = 1) (hb : d326236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d326236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319704, d326236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319708 q = 1) (hb : d326240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319708, d326240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88797 q ha hb
    | true =>
      simp only [d319708, d326240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88798 q ha hb
  have h17 (q : Pattern) (ha : d319709 q = 1) (hb : d326241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319709, d326241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319709, d326241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319710 q = 1) (hb : d326242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319710, d326242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319710, d326242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d319711 q = 1) (hb : d326243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319711, d326243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319711, d326243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d319714 q = 1) (hb : d326246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319714, d326246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88799 q ha hb
    | true =>
      simp only [d319714, d326246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88800 q ha hb
  have h21 (q : Pattern) (ha : d319715 q = 1) (hb : d326247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319715, d326247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319715, d326247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d319716 q = 1) (hb : d326248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319716, d326248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319716, d326248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d319718 q = 1) (hb : d326250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319718, d326250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88801 q ha hb
    | true =>
      simp only [d319718, d326250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88778 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d319719 q = 1) (hb : d326251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d326251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d319719, d326251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d319721 q = 1) (hb : d326253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319721, d326253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88802 q ha hb
    | true =>
      simp only [d319721, d326253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d319722 q = 1) (hb : d326254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319722, d326254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d319722, d326254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d319723 q = 1) (hb : d326255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d326255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d319723, d326255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d319724 q = 1) (hb : d326256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319724, d326256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d319724, d326256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d319725 q = 1) (hb : d326257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319725, d326257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319725, d326257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d319726 q = 1) (hb : d326258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319726, d326258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319726, d326258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro88804 (p : Pattern) (ha : d319733 p = 1) (hb : d326265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319593 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
    | true =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
  have h2 (q : Pattern) (ha : d319594 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319594, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319594, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319595 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319595, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319595, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319596 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319596, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319596, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319597 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319597, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319597, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319728 q = 1) (hb : d326260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319728, d326260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
    | true =>
      simp only [d319728, d326260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319729 q = 1) (hb : d326261 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319729, d326261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319729, d326261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319730 q = 1) (hb : d326262 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319730, d326262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319730, d326262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319731 q = 1) (hb : d326263 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319731, d326263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319731, d326263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319732 q = 1) (hb : d326264 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319732, d326264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319732, d326264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319733 q = 1) (hb : d326265 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319733, d326265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319733, d326265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88805 (p : Pattern) (ha : d319739 p = 1) (hb : d326271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319728 q = 1) (hb : d326260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319728, d326260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
    | true =>
      simp only [d319728, d326260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319729 q = 1) (hb : d326261 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319729, d326261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319729, d326261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319730 q = 1) (hb : d326262 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319730, d326262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319730, d326262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319731 q = 1) (hb : d326263 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319731, d326263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319731, d326263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319732 q = 1) (hb : d326264 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319732, d326264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319732, d326264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319734 q = 1) (hb : d326266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319734, d326266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88779 q ha hb
    | true =>
      simp only [d319734, d326266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319735 q = 1) (hb : d326267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319735, d326267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319735, d326267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319736 q = 1) (hb : d326268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319736, d326268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319736, d326268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319737 q = 1) (hb : d326269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319737, d326269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319737, d326269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319738 q = 1) (hb : d326270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319738, d326270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319738, d326270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319739 q = 1) (hb : d326271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319739, d326271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319739, d326271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88806 (p : Pattern) (ha : d319746 p = 1) (hb : d326278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319718 q = 1) (hb : d326250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319718, d326250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88801 q ha hb
    | true =>
      simp only [d319718, d326250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88778 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319719 q = 1) (hb : d326251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d326251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319719, d326251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319721 q = 1) (hb : d326253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319721, d326253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88802 q ha hb
    | true =>
      simp only [d319721, d326253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319722 q = 1) (hb : d326254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319722, d326254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319722, d326254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319723 q = 1) (hb : d326255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d326255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319723, d326255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319744 q = 1) (hb : d326276 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319744, d326276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319744, d326276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319745 q = 1) (hb : d326277 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319745, d326277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319745, d326277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319746 q = 1) (hb : d326278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319746, d326278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319746, d326278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro88807 (p : Pattern) (ha : d319748 p = 1) (hb : d326280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319734 q = 1) (hb : d326266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319734, d326266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88779 q ha hb
    | true =>
      simp only [d319734, d326266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319735 q = 1) (hb : d326267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319735, d326267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319735, d326267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319736 q = 1) (hb : d326268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319736, d326268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319736, d326268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319737 q = 1) (hb : d326269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319737, d326269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319737, d326269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319738 q = 1) (hb : d326270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319738, d326270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319738, d326270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319748 q = 1) (hb : d326280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319748, d326280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319748, d326280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88808 (p : Pattern) (ha : d319772 p = 1) (hb : d326304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319754 q = 1) (hb : d326286 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319754, d326286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319754, d326286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88785 q ha hb
  have h2 (q : Pattern) (ha : d319633 q = 1) (hb : d326172 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319633, d326172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88785 q ha hb
    | true =>
      simp only [d319633, d326172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319755 q = 1) (hb : d326287 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319755, d326287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319755, d326287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319634 q = 1) (hb : d326173 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319634, d326173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319634, d326173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319756 q = 1) (hb : d326288 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319756, d326288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319756, d326288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319757 q = 1) (hb : d326289 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319757, d326289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319757, d326289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319758 q = 1) (hb : d326290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319758, d326290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319758, d326290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88786 q ha hb
  have h8 (q : Pattern) (ha : d319645 q = 1) (hb : d326180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319645, d326180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88786 q ha hb
    | true =>
      simp only [d319645, d326180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319759 q = 1) (hb : d326291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319759, d326291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319759, d326291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319646 q = 1) (hb : d326181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319646, d326181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319646, d326181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319760 q = 1) (hb : d326292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319760, d326292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319760, d326292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319761 q = 1) (hb : d326293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319761, d326293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319761, d326293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319762 q = 1) (hb : d326294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319762, d326294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319762, d326294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319763 q = 1) (hb : d326295 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319763, d326295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319763, d326295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88787 q ha hb
  have h15 (q : Pattern) (ha : d319654 q = 1) (hb : d326186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319654, d326186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88787 q ha hb
    | true =>
      simp only [d319654, d326186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319764 q = 1) (hb : d326296 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319764, d326296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319764, d326296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319655 q = 1) (hb : d326187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319655, d326187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319655, d326187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d319765 q = 1) (hb : d326297 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319765, d326297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319765, d326297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d319766 q = 1) (hb : d326298 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319766, d326298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d319766, d326298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d319767 q = 1) (hb : d326299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319767, d326299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319767, d326299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88766 q ha hb
  have h21 (q : Pattern) (ha : d319534 q = 1) (hb : d326076 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88766 q ha hb
    | true =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319768 q = 1) (hb : d326300 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319768, d326300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319768, d326300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d319535 q = 1) (hb : d326077 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d319769 q = 1) (hb : d326301 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319769, d326301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d319769, d326301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d319770 q = 1) (hb : d326302 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319770, d326302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d319770, d326302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d319771 q = 1) (hb : d326303 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319771, d326303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319771, d326303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d319772 q = 1) (hb : d326304 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319772, d326304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319772, d326304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro88809 (p : Pattern) (ha : d319787 p = 1) (hb : d326319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319773 q = 1) (hb : d326305 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319773, d326305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319773, d326305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88764 q ha hb
  have h2 (q : Pattern) (ha : d319513 q = 1) (hb : d326057 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319513, d326057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88764 q ha hb
    | true =>
      simp only [d319513, d326057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319774 q = 1) (hb : d326306 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319774, d326306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319774, d326306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319514 q = 1) (hb : d326058 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319514, d326058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319514, d326058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319775 q = 1) (hb : d326307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319775, d326307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319775, d326307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319776 q = 1) (hb : d326308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319776, d326308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319776, d326308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319777 q = 1) (hb : d326309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319777, d326309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319777, d326309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88765 q ha hb
  have h8 (q : Pattern) (ha : d319525 q = 1) (hb : d326067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319525, d326067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88765 q ha hb
    | true =>
      simp only [d319525, d326067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319778 q = 1) (hb : d326310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319778, d326310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319778, d326310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319526 q = 1) (hb : d326068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319526, d326068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319526, d326068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319779 q = 1) (hb : d326311 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319779, d326311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319779, d326311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319780 q = 1) (hb : d326312 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319780, d326312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319780, d326312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319781 q = 1) (hb : d326313 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319781, d326313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319781, d326313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319767 q = 1) (hb : d326299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319767, d326299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319767, d326299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88766 q ha hb
  have h15 (q : Pattern) (ha : d319534 q = 1) (hb : d326076 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88766 q ha hb
    | true =>
      simp only [d319534, d326076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319768 q = 1) (hb : d326300 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319768, d326300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319768, d326300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319535 q = 1) (hb : d326077 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319535, d326077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d319769 q = 1) (hb : d326301 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319769, d326301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319769, d326301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d319770 q = 1) (hb : d326302 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319770, d326302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d319770, d326302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d319782 q = 1) (hb : d326314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319782, d326314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319782, d326314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
  have h21 (q : Pattern) (ha : d319543 q = 1) (hb : d326085 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
    | true =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319783 q = 1) (hb : d326315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319783, d326315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319783, d326315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d319544 q = 1) (hb : d326086 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d319784 q = 1) (hb : d326316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319784, d326316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d319784, d326316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d319785 q = 1) (hb : d326317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319785, d326317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d319785, d326317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d319786 q = 1) (hb : d326318 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319786, d326318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319786, d326318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d319787 q = 1) (hb : d326319 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319787, d326319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319787, d326319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro88810 (p : Pattern) (ha : d319797 p = 1) (hb : d326329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319791 q = 1) (hb : d326323 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319791, d326323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319791, d326323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88789 q ha hb
  have h2 (q : Pattern) (ha : d319667 q = 1) (hb : d326199 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319667, d326199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88789 q ha hb
    | true =>
      simp only [d319667, d326199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319792 q = 1) (hb : d326324 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319792, d326324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319792, d326324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319668 q = 1) (hb : d326200 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319668, d326200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319668, d326200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319793 q = 1) (hb : d326325 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319793, d326325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319793, d326325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319794 q = 1) (hb : d326326 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319794, d326326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319794, d326326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319782 q = 1) (hb : d326314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319782, d326314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319782, d326314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
  have h8 (q : Pattern) (ha : d319543 q = 1) (hb : d326085 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
    | true =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319783 q = 1) (hb : d326315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319783, d326315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319783, d326315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319544 q = 1) (hb : d326086 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319784 q = 1) (hb : d326316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319784, d326316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319784, d326316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319785 q = 1) (hb : d326317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319785, d326317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319785, d326317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319795 q = 1) (hb : d326327 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319795, d326327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319795, d326327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319796 q = 1) (hb : d326328 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319796, d326328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319796, d326328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319797 q = 1) (hb : d326329 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319797, d326329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319797, d326329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88811 (p : Pattern) (ha : d319811 p = 1) (hb : d326343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319802 q = 1) (hb : d326334 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319802, d326334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319802, d326334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88769 q ha hb
  have h2 (q : Pattern) (ha : d319555 q = 1) (hb : d326097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319555, d326097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88769 q ha hb
    | true =>
      simp only [d319555, d326097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319803 q = 1) (hb : d326335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319803, d326335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319803, d326335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319556 q = 1) (hb : d326098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319556, d326098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319556, d326098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319804 q = 1) (hb : d326336 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319804, d326336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319804, d326336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319805 q = 1) (hb : d326337 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319805, d326337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319805, d326337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319806 q = 1) (hb : d326338 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319806, d326338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319806, d326338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
  have h8 (q : Pattern) (ha : d319560 q = 1) (hb : d326102 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
    | true =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319807 q = 1) (hb : d326339 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319807, d326339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319807, d326339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319561 q = 1) (hb : d326103 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319808 q = 1) (hb : d326340 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319808, d326340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319808, d326340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319809 q = 1) (hb : d326341 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319809, d326341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319809, d326341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d319810 q = 1) (hb : d326342 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319810, d326342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319810, d326342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319782 q = 1) (hb : d326314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319782, d326314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319782, d326314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
  have h15 (q : Pattern) (ha : d319543 q = 1) (hb : d326085 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88767 q ha hb
    | true =>
      simp only [d319543, d326085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319783 q = 1) (hb : d326315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319783, d326315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319783, d326315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319544 q = 1) (hb : d326086 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319544, d326086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d319784 q = 1) (hb : d326316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319784, d326316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319784, d326316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d319785 q = 1) (hb : d326317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319785, d326317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d319785, d326317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d319796 q = 1) (hb : d326328 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319796, d326328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319796, d326328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d319811 q = 1) (hb : d326343 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319811, d326343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319811, d326343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro88812 (p : Pattern) (ha : d319816 p = 1) (hb : d326348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319806 q = 1) (hb : d326338 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319806, d326338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319806, d326338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
  have h2 (q : Pattern) (ha : d319560 q = 1) (hb : d326102 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
    | true =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319807 q = 1) (hb : d326339 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319807, d326339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319807, d326339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319561 q = 1) (hb : d326103 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319808 q = 1) (hb : d326340 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319808, d326340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319808, d326340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319809 q = 1) (hb : d326341 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319809, d326341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319809, d326341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319815 q = 1) (hb : d326347 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319815, d326347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319815, d326347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d319816 q = 1) (hb : d326348 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319816, d326348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319816, d326348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro88813 (p : Pattern) (ha : d319822 p = 1) (hb : d326354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319788 q = 1) (hb : d326320 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319788, d326320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88808 q ha hb
    | true =>
      simp only [d319788, d326320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88809 q ha hb
  have h2 (q : Pattern) (ha : d319789 q = 1) (hb : d326321 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319789, d326321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319789, d326321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319790 q = 1) (hb : d326322 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319790, d326322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319790, d326322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319798 q = 1) (hb : d326330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319798, d326330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88809 q ha hb
    | true =>
      simp only [d319798, d326330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88810 q ha hb
  have h5 (q : Pattern) (ha : d319799 q = 1) (hb : d326331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319799, d326331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319799, d326331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319800 q = 1) (hb : d326332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319800, d326332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319800, d326332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319801 q = 1) (hb : d326333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319801, d326333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319801, d326333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319812 q = 1) (hb : d326344 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319812, d326344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88809 q ha hb
    | true =>
      simp only [d319812, d326344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
  have h9 (q : Pattern) (ha : d319813 q = 1) (hb : d326345 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319813, d326345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319813, d326345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319814 q = 1) (hb : d326346 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319814, d326346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319814, d326346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319817 q = 1) (hb : d326349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
    | true =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88812 q ha hb
  have h12 (q : Pattern) (ha : d319818 q = 1) (hb : d326350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319819 q = 1) (hb : d326351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319820 q = 1) (hb : d326352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319820, d326352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319820, d326352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319821 q = 1) (hb : d326353 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319821, d326353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319821, d326353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319822 q = 1) (hb : d326354 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319822, d326354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319822, d326354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro88814 (p : Pattern) (ha : d319827 p = 1) (hb : d326359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319812 q = 1) (hb : d326344 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319812, d326344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88809 q ha hb
    | true =>
      simp only [d319812, d326344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
  have h2 (q : Pattern) (ha : d319813 q = 1) (hb : d326345 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319813, d326345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319813, d326345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319814 q = 1) (hb : d326346 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319814, d326346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319814, d326346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319817 q = 1) (hb : d326349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
    | true =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88812 q ha hb
  have h5 (q : Pattern) (ha : d319818 q = 1) (hb : d326350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319819 q = 1) (hb : d326351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319820 q = 1) (hb : d326352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319820, d326352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319820, d326352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319825 q = 1) (hb : d326357 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319825, d326357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319825, d326357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319826 q = 1) (hb : d326358 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319826, d326358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319826, d326358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319827 q = 1) (hb : d326359 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319827, d326359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319827, d326359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro88815 (p : Pattern) (ha : d319833 p = 1) (hb : d326365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319823 q = 1) (hb : d326355 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319823, d326355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88813 q ha hb
    | true =>
      simp only [d319823, d326355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319824 q = 1) (hb : d326356 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319824, d326356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319824, d326356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319828 q = 1) (hb : d326360 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319828, d326360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88814 q ha hb
    | true =>
      simp only [d319828, d326360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319829 q = 1) (hb : d326361 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319829, d326361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319829, d326361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319830 q = 1) (hb : d326362 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319830, d326362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319830, d326362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319831 q = 1) (hb : d326363 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319831, d326363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319831, d326363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319832 q = 1) (hb : d326364 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319832, d326364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319832, d326364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319833 q = 1) (hb : d326365 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319833, d326365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319833, d326365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88816 (p : Pattern) (ha : d319835 p = 1) (hb : d326367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319817 q = 1) (hb : d326349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
    | true =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88812 q ha hb
  have h2 (q : Pattern) (ha : d319818 q = 1) (hb : d326350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319819 q = 1) (hb : d326351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319825 q = 1) (hb : d326357 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319825, d326357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319825, d326357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319834 q = 1) (hb : d326366 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319834, d326366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319834, d326366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319835 q = 1) (hb : d326367 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319835, d326367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319835, d326367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88817 (p : Pattern) (ha : d319841 p = 1) (hb : d326373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319828 q = 1) (hb : d326360 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319828, d326360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88814 q ha hb
    | true =>
      simp only [d319828, d326360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319829 q = 1) (hb : d326361 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319829, d326361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319829, d326361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319836 q = 1) (hb : d326368 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319836, d326368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88816 q ha hb
    | true =>
      simp only [d319836, d326368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319837 q = 1) (hb : d326369 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319837, d326369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319837, d326369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319838 q = 1) (hb : d326370 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319838, d326370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319838, d326370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319839 q = 1) (hb : d326371 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319839, d326371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319839, d326371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319840 q = 1) (hb : d326372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319840, d326372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319840, d326372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319841 q = 1) (hb : d326373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319841, d326373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319841, d326373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88818 (p : Pattern) (ha : d319849 p = 1) (hb : d326376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319806 q = 1) (hb : d326338 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319806, d326338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319806, d326338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
  have h2 (q : Pattern) (ha : d319560 q = 1) (hb : d326102 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88770 q ha hb
    | true =>
      simp only [d319560, d326102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319807 q = 1) (hb : d326339 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319807, d326339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319807, d326339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319561 q = 1) (hb : d326103 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319561, d326103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319808 q = 1) (hb : d326340 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319808, d326340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319808, d326340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319809 q = 1) (hb : d326341 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319809, d326341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319809, d326341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319815 q = 1) (hb : d326347 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319815, d326347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319815, d326347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319849 q = 1) (hb : d326376 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319849, d326376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319849, d326376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88819 (p : Pattern) (ha : d319855 p = 1) (hb : d326382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319812 q = 1) (hb : d326344 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319812, d326344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88809 q ha hb
    | true =>
      simp only [d319812, d326344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
  have h2 (q : Pattern) (ha : d319813 q = 1) (hb : d326345 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319813, d326345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319813, d326345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319814 q = 1) (hb : d326346 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319814, d326346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319814, d326346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319817 q = 1) (hb : d326349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
    | true =>
      simp only [d319817, d326349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88812 q ha hb
  have h5 (q : Pattern) (ha : d319818 q = 1) (hb : d326350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319818, d326350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319819 q = 1) (hb : d326351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319819, d326351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319820 q = 1) (hb : d326352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319820, d326352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319820, d326352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319850 q = 1) (hb : d326377 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319850, d326377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88811 q ha hb
    | true =>
      simp only [d319850, d326377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88818 q ha hb
  have h9 (q : Pattern) (ha : d319851 q = 1) (hb : d326378 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319851, d326378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319851, d326378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319852 q = 1) (hb : d326379 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319852, d326379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319852, d326379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319853 q = 1) (hb : d326380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319853, d326380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319853, d326380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d319854 q = 1) (hb : d326381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319854, d326381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319854, d326381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319855 q = 1) (hb : d326382 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319855, d326382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319855, d326382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro88820 (p : Pattern) (ha : d319861 p = 1) (hb : d326388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319856 q = 1) (hb : d326383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319856, d326383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88819 q ha hb
    | true =>
      simp only [d319856, d326383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319857 q = 1) (hb : d326384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319857, d326384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319857, d326384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319858 q = 1) (hb : d326385 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319858, d326385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319858, d326385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319859 q = 1) (hb : d326386 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319859, d326386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319859, d326386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319860 q = 1) (hb : d326387 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319860, d326387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319860, d326387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319861 q = 1) (hb : d326388 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319861, d326388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319861, d326388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88821 (p : Pattern) (ha : d319867 p = 1) (hb : d326394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319842 q = 1) (hb : d326374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319842, d326374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88815 q ha hb
    | true =>
      simp only [d319842, d326374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88817 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319848 q = 1) (hb : d326375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319848, d326375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319848, d326375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319862 q = 1) (hb : d326389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319862, d326389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88820 q ha hb
    | true =>
      simp only [d319862, d326389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319863 q = 1) (hb : d326390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319863, d326390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319863, d326390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319864 q = 1) (hb : d326391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319864, d326391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319864, d326391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319865 q = 1) (hb : d326392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319865, d326392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319865, d326392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319866 q = 1) (hb : d326393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319866, d326393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319866, d326393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319867 q = 1) (hb : d326394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319867, d326394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319867, d326394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro88822 (p : Pattern) (ha : d319846 p = 1) (hb : d326399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319836 q = 1) (hb : d326368 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319836, d326368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88816 q ha hb
    | true =>
      simp only [d319836, d326368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319837 q = 1) (hb : d326369 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319837, d326369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319837, d326369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319843 q = 1) (hb : d326396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319843, d326396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319843, d326396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319844 q = 1) (hb : d326397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319844, d326397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319844, d326397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319845 q = 1) (hb : d326398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319845, d326398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319845, d326398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319846 q = 1) (hb : d326399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319846, d326399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319846, d326399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88823 (p : Pattern) (ha : d319874 p = 1) (hb : d326405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319869 q = 1) (hb : d326400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319869, d326400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88822 q ha hb
    | true =>
      simp only [d319869, d326400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319870 q = 1) (hb : d326401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319870, d326401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319870, d326401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319871 q = 1) (hb : d326402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319871, d326402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319871, d326402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319872 q = 1) (hb : d326403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319872, d326403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319872, d326403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319873 q = 1) (hb : d326404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319873, d326404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319873, d326404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319874 q = 1) (hb : d326405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319874, d326405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319874, d326405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88824 (p : Pattern) (ha : d319880 p = 1) (hb : d326411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319599 q = 1) (hb : d326141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319599, d326141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319599, d326141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88777 q ha hb
  have h2 (q : Pattern) (ha : d319600 q = 1) (hb : d326142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319600, d326142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319600, d326142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319609 q = 1) (hb : d326151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319609, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88777 q ha hb
    | true =>
      simp only [d319609, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88780 q ha hb
  have h4 (q : Pattern) (ha : d319610 q = 1) (hb : d326152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319610, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319610, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319611 q = 1) (hb : d326153 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319611, d326153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319611, d326153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319727 q = 1) (hb : d326259 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319727, d326259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88796 q ha hb
    | true =>
      simp only [d319727, d326259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88803 q ha hb
  have h7 (q : Pattern) (ha : d319740 q = 1) (hb : d326272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319740, d326272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88804 q ha hb
    | true =>
      simp only [d319740, d326272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88805 q ha hb
  have h8 (q : Pattern) (ha : d319741 q = 1) (hb : d326273 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319741, d326273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319741, d326273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319742 q = 1) (hb : d326274 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319742, d326274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319742, d326274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d319743 q = 1) (hb : d326275 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319743, d326275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319743, d326275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319747 q = 1) (hb : d326279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319747, d326279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319747, d326279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88806 q ha hb
  have h12 (q : Pattern) (ha : d319749 q = 1) (hb : d326281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319749, d326281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319749, d326281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88807 q ha hb
  have h13 (q : Pattern) (ha : d319750 q = 1) (hb : d326282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319750, d326282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319750, d326282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d319751 q = 1) (hb : d326283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319751, d326283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319751, d326283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319752 q = 1) (hb : d326284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319752, d326284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319752, d326284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319753 q = 1) (hb : d326285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319753, d326285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319753, d326285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319868 q = 1) (hb : d326395 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319868, d326395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319868, d326395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88821 q ha hb
  have h18 (q : Pattern) (ha : d319875 q = 1) (hb : d326406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319875, d326406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319875, d326406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88823 q ha hb
  have h19 (q : Pattern) (ha : d319876 q = 1) (hb : d326407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319876, d326407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319876, d326407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d319877 q = 1) (hb : d326408 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319877, d326408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319877, d326408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d319878 q = 1) (hb : d326409 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319878, d326409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319878, d326409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319879 q = 1) (hb : d326410 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319879, d326410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319879, d326410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d319880 q = 1) (hb : d326411 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319880, d326411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319880, d326411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro88825 (p : Pattern) (ha : d319886 p = 1) (hb : d326417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319881 q = 1) (hb : d326412 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319881, d326412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319881, d326412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88824 q ha hb
  have h2 (q : Pattern) (ha : d319882 q = 1) (hb : d326413 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319882, d326413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319882, d326413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319883 q = 1) (hb : d326414 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319883, d326414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319883, d326414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319884 q = 1) (hb : d326415 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319884, d326415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319884, d326415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319885 q = 1) (hb : d326416 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319885, d326416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319885, d326416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319886 q = 1) (hb : d326417 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319886, d326417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319886, d326417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88826 (p : Pattern) (ha : d319897 p = 1) (hb : d324616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d319893 q = 1) (hb : d324612 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319893, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319893, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319894 q = 1) (hb : d324613 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319894, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319894, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319895 q = 1) (hb : d324614 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319895, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319895, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319896 q = 1) (hb : d324615 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319896, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319896, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319897 q = 1) (hb : d324616 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319897, d324616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319897, d324616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro88827 (p : Pattern) (ha : d319913 p = 1) (hb : d324622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319892 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d319893 q = 1) (hb : d324612 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319893, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319893, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319894 q = 1) (hb : d324613 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319894, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319894, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319895 q = 1) (hb : d324614 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319895, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319895, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d319896 q = 1) (hb : d324615 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319896, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319896, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d319905 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h9 (q : Pattern) (ha : d221076 q = 1) (hb : d319906 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d221076, d319906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d221076, d319906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d221096 q = 1) (hb : d319907 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d221096, d319907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d221096, d319907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319908 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d221097 q = 1) (hb : d319909 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d221097, d319909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d221097, d319909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d221098 q = 1) (hb : d319910 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d221098, d319910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d221098, d319910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d221099 q = 1) (hb : d319911 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d221099, d319911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d221099, d319911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d221100 q = 1) (hb : d319912 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d221100, d319912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d221100, d319912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d319913 q = 1) (hb : d324622 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d319913, d324622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319913, d324622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro88828 (p : Pattern) (ha : d319919 p = 1) (hb : d324628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319900 q = 1) (hb : d324619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319901 q = 1) (hb : d324620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319902 q = 1) (hb : d324621 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319902, d324621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319902, d324621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319916 q = 1) (hb : d324625 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319917 q = 1) (hb : d324626 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d319918 q = 1) (hb : d324627 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319918, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319918, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319919 q = 1) (hb : d324628 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319919, d324628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319919, d324628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88829 (p : Pattern) (ha : d319921 p = 1) (hb : d324630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319900 q = 1) (hb : d324619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319901 q = 1) (hb : d324620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319916 q = 1) (hb : d324625 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319917 q = 1) (hb : d324626 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319918 q = 1) (hb : d324627 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319918, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319918, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319920 q = 1) (hb : d324629 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319920, d324629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319920, d324629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d319921 q = 1) (hb : d324630 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319921, d324630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319921, d324630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88830 (p : Pattern) (ha : d221101 p = 1) (hb : d319925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319905 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h3 (q : Pattern) (ha : d221076 q = 1) (hb : d319906 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d221076, d319906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d221076, d319906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d221096 q = 1) (hb : d319907 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d221096, d319907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d221096, d319907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d221097 q = 1) (hb : d319909 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d221097, d319909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d221097, d319909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d221098 q = 1) (hb : d319910 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d221098, d319910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d221098, d319910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d221099 q = 1) (hb : d319911 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d221099, d319911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d221099, d319911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d221100 q = 1) (hb : d319912 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d221100, d319912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d221100, d319912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d221101 q = 1) (hb : d319925 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d221101, d319925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d221101, d319925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h11 p ha hb
theorem andIntro88831 (p : Pattern) (ha : d319931 p = 1) (hb : d324634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319916 q = 1) (hb : d324625 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319917 q = 1) (hb : d324626 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319920 q = 1) (hb : d324629 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319920, d324629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319920, d324629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d221102 q = 1) (hb : d319926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221102, d319926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88830 q ha hb
    | true =>
      simp only [d221102, d319926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d221103 q = 1) (hb : d319927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221103, d319927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d221103, d319927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d221104 q = 1) (hb : d319928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d221104, d319928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d221104, d319928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d221105 q = 1) (hb : d319929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d221105, d319929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d221105, d319929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d221106 q = 1) (hb : d319930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d221106, d319930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d221106, d319930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d319931 q = 1) (hb : d324634 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319931, d324634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319931, d324634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro88832 (p : Pattern) (ha : d319938 p = 1) (hb : d324641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319922 q = 1) (hb : d324631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319922, d324631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88828 q ha hb
    | true =>
      simp only [d319922, d324631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
  have h2 (q : Pattern) (ha : d319923 q = 1) (hb : d324632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319923, d324632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319923, d324632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319924 q = 1) (hb : d324633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319924, d324633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319924, d324633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319932 q = 1) (hb : d324635 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
    | true =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88831 q ha hb
  have h5 (q : Pattern) (ha : d319933 q = 1) (hb : d324636 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319934 q = 1) (hb : d324637 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319935 q = 1) (hb : d324638 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319935, d324638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319935, d324638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319936 q = 1) (hb : d324639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319936, d324639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319936, d324639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319937 q = 1) (hb : d324640 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319937, d324640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319937, d324640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319938 q = 1) (hb : d324641 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319938, d324641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319938, d324641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro88833 (p : Pattern) (ha : d319942 p = 1) (hb : d324645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319932 q = 1) (hb : d324635 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
    | true =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88831 q ha hb
  have h2 (q : Pattern) (ha : d319933 q = 1) (hb : d324636 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319934 q = 1) (hb : d324637 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319936 q = 1) (hb : d324639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319936, d324639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319936, d324639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319941 q = 1) (hb : d324644 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319941, d324644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319941, d324644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319942 q = 1) (hb : d324645 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319942, d324645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319942, d324645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88834 (p : Pattern) (ha : d319948 p = 1) (hb : d324651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319945 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319946 q = 1) (hb : d324649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319947 q = 1) (hb : d324650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319947, d324650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319947, d324650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319948 q = 1) (hb : d324651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319948, d324651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319948, d324651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88835 (p : Pattern) (ha : d319952 p = 1) (hb : d324655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319949 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319950 q = 1) (hb : d324653 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319951 q = 1) (hb : d324654 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319951, d324654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319951, d324654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319952 q = 1) (hb : d324655 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319952, d324655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319952, d324655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88836 (p : Pattern) (ha : d319958 p = 1) (hb : d324661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319953 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
    | true =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
  have h2 (q : Pattern) (ha : d319954 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319954, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319954, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319955 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319955, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319955, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319956 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319956, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319956, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319957 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319957, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319957, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319958 q = 1) (hb : d324661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319958, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319958, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88837 (p : Pattern) (ha : d319961 p = 1) (hb : d324664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319945 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319946 q = 1) (hb : d324649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319947 q = 1) (hb : d324650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319947, d324650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319947, d324650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319961 q = 1) (hb : d324664 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319961, d324664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319961, d324664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88838 (p : Pattern) (ha : d319962 p = 1) (hb : d324665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319949 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319950 q = 1) (hb : d324653 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319951 q = 1) (hb : d324654 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319951, d324654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319951, d324654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319962 q = 1) (hb : d324665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319962, d324665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319962, d324665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88839 (p : Pattern) (ha : d319968 p = 1) (hb : d324671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319953 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
    | true =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
  have h2 (q : Pattern) (ha : d319954 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319954, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319954, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319955 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319955, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319955, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319956 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319956, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319956, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319957 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319957, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319957, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319963 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319963, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88837 q ha hb
    | true =>
      simp only [d319963, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88838 q ha hb
  have h7 (q : Pattern) (ha : d319964 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319964, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319964, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319965 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319965, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319965, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319966 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319966, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319966, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319967 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319967, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319967, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319968 q = 1) (hb : d324671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319968, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319968, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88840 (p : Pattern) (ha : d319973 p = 1) (hb : d324676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319945 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319946 q = 1) (hb : d324649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319972 q = 1) (hb : d324675 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319972, d324675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319972, d324675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319973 q = 1) (hb : d324676 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319973, d324676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319973, d324676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88841 (p : Pattern) (ha : d319975 p = 1) (hb : d324678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319949 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319950 q = 1) (hb : d324653 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319974 q = 1) (hb : d324677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319974, d324677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319974, d324677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319975 q = 1) (hb : d324678 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319975, d324678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319975, d324678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88842 (p : Pattern) (ha : d319982 p = 1) (hb : d324685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319945 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319980 q = 1) (hb : d324683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319980, d324683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319980, d324683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319981 q = 1) (hb : d324684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319981, d324684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319981, d324684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d319982 q = 1) (hb : d324685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319982, d324685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319982, d324685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88843 (p : Pattern) (ha : d319985 p = 1) (hb : d324688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319949 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319983 q = 1) (hb : d324686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319983, d324686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319983, d324686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319984 q = 1) (hb : d324687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319984, d324687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319984, d324687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319985 q = 1) (hb : d324688 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d319985, d324688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319985, d324688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88844 (p : Pattern) (ha : d319989 p = 1) (hb : d324692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319900 q = 1) (hb : d324619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319901 q = 1) (hb : d324620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319902 q = 1) (hb : d324621 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319902, d324621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319902, d324621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319989 q = 1) (hb : d324692 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d319989, d324692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319989, d324692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88845 (p : Pattern) (ha : d319995 p = 1) (hb : d324698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319990 q = 1) (hb : d324693 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319990, d324693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88844 q ha hb
    | true =>
      simp only [d319990, d324693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88828 q ha hb
  have h2 (q : Pattern) (ha : d319991 q = 1) (hb : d324694 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319991, d324694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319991, d324694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319992 q = 1) (hb : d324695 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319992, d324695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319992, d324695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319922 q = 1) (hb : d324631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319922, d324631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88828 q ha hb
    | true =>
      simp only [d319922, d324631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
  have h5 (q : Pattern) (ha : d319923 q = 1) (hb : d324632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319923, d324632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319923, d324632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319924 q = 1) (hb : d324633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319924, d324633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319924, d324633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319993 q = 1) (hb : d324696 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319993, d324696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319993, d324696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319932 q = 1) (hb : d324635 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
    | true =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88831 q ha hb
  have h9 (q : Pattern) (ha : d319933 q = 1) (hb : d324636 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319934 q = 1) (hb : d324637 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319935 q = 1) (hb : d324638 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319935, d324638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319935, d324638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d319994 q = 1) (hb : d324697 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d319994, d324697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319994, d324697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319995 q = 1) (hb : d324698 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d319995, d324698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319995, d324698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro88846 (p : Pattern) (ha : d320001 p = 1) (hb : d324704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319996 q = 1) (hb : d324699 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319996, d324699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88845 q ha hb
    | true =>
      simp only [d319996, d324699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319997 q = 1) (hb : d324700 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319997, d324700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319997, d324700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319998 q = 1) (hb : d324701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319998, d324701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319998, d324701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319999 q = 1) (hb : d324702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319999, d324702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319999, d324702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320000 q = 1) (hb : d324703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320000, d324703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320000, d324703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320001 q = 1) (hb : d324704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320001, d324704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320001, d324704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88847 (p : Pattern) (ha : d320004 p = 1) (hb : d324707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319892 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d319893 q = 1) (hb : d324612 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d319893, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319893, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d319894 q = 1) (hb : d324613 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d319894, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319894, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d319895 q = 1) (hb : d324614 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d319895, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319895, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d319896 q = 1) (hb : d324615 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d319896, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319896, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d320004 q = 1) (hb : d324707 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d320004, d324707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320004, d324707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro88848 (p : Pattern) (ha : d320010 p = 1) (hb : d324713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319900 q = 1) (hb : d324619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319900, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319901 q = 1) (hb : d324620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319901, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319916 q = 1) (hb : d324625 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319916, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319917 q = 1) (hb : d324626 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319917, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d319918 q = 1) (hb : d324627 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d319918, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319918, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320005 q = 1) (hb : d324708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88847 q ha hb
    | true =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d320006 q = 1) (hb : d324709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320007 q = 1) (hb : d324710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320007, d324710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320007, d324710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320008 q = 1) (hb : d324711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320008, d324711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320008, d324711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d320009 q = 1) (hb : d324712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320009, d324712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320009, d324712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d320010 q = 1) (hb : d324713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320010, d324713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320010, d324713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88849 (p : Pattern) (ha : d320011 p = 1) (hb : d324714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320005 q = 1) (hb : d324708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88847 q ha hb
    | true =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320006 q = 1) (hb : d324709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320007 q = 1) (hb : d324710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320007, d324710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320007, d324710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320008 q = 1) (hb : d324711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320008, d324711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320008, d324711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320009 q = 1) (hb : d324712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320009, d324712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320009, d324712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320011 q = 1) (hb : d324714 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320011, d324714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320011, d324714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88850 (p : Pattern) (ha : d320017 p = 1) (hb : d324720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319922 q = 1) (hb : d324631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319922, d324631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88828 q ha hb
    | true =>
      simp only [d319922, d324631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
  have h2 (q : Pattern) (ha : d319923 q = 1) (hb : d324632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319923, d324632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319923, d324632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319924 q = 1) (hb : d324633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319924, d324633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319924, d324633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319932 q = 1) (hb : d324635 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88829 q ha hb
    | true =>
      simp only [d319932, d324635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88831 q ha hb
  have h5 (q : Pattern) (ha : d319933 q = 1) (hb : d324636 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319933, d324636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319934 q = 1) (hb : d324637 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319934, d324637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319935 q = 1) (hb : d324638 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d319935, d324638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319935, d324638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320012 q = 1) (hb : d324715 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320012, d324715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88848 q ha hb
    | true =>
      simp only [d320012, d324715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88849 q ha hb
  have h9 (q : Pattern) (ha : d320013 q = 1) (hb : d324716 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320013, d324716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320013, d324716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320014 q = 1) (hb : d324717 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320014, d324717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320014, d324717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320015 q = 1) (hb : d324718 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320015, d324718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320015, d324718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320016 q = 1) (hb : d324719 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320016, d324719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320016, d324719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320017 q = 1) (hb : d324720 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320017, d324720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320017, d324720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro88851 (p : Pattern) (ha : d320023 p = 1) (hb : d324726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320018 q = 1) (hb : d324721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320018, d324721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88850 q ha hb
    | true =>
      simp only [d320018, d324721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320019 q = 1) (hb : d324722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320019, d324722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320019, d324722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320020 q = 1) (hb : d324723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320020, d324723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320020, d324723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320021 q = 1) (hb : d324724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320021, d324724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320021, d324724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320022 q = 1) (hb : d324725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320022, d324725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320022, d324725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320023 q = 1) (hb : d324726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320023, d324726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320023, d324726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88852 (p : Pattern) (ha : d320029 p = 1) (hb : d324732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319976 q = 1) (hb : d324679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319976, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88840 q ha hb
    | true =>
      simp only [d319976, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88841 q ha hb
  have h2 (q : Pattern) (ha : d319977 q = 1) (hb : d324680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319977, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319977, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319978 q = 1) (hb : d324681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319978, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319978, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319979 q = 1) (hb : d324682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319979, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319979, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319986 q = 1) (hb : d324689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319986, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88842 q ha hb
    | true =>
      simp only [d319986, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88843 q ha hb
  have h6 (q : Pattern) (ha : d319987 q = 1) (hb : d324690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319987, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319987, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319988 q = 1) (hb : d324691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319988, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319988, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320002 q = 1) (hb : d324705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320002, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88846 q ha hb
    | true =>
      simp only [d320002, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319953 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d320003 q = 1) (hb : d324706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320003, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320003, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d320024 q = 1) (hb : d324727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320024, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88851 q ha hb
    | true =>
      simp only [d320024, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320025 q = 1) (hb : d324728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320025, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320025, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d320026 q = 1) (hb : d324729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320026, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320026, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320027 q = 1) (hb : d324730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320027, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320027, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320028 q = 1) (hb : d324731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320028, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320028, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320029 q = 1) (hb : d324732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320029, d324732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320029, d324732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro88853 (p : Pattern) (ha : d320030 p = 1) (hb : d324733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319945 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319946 q = 1) (hb : d324649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319946, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d319972 q = 1) (hb : d324675 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319972, d324675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319972, d324675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320030 q = 1) (hb : d324733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320030, d324733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320030, d324733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88854 (p : Pattern) (ha : d320031 p = 1) (hb : d324734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319949 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319950 q = 1) (hb : d324653 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319950, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319974 q = 1) (hb : d324677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319974, d324677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319974, d324677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320031 q = 1) (hb : d324734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320031, d324734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320031, d324734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88855 (p : Pattern) (ha : d320036 p = 1) (hb : d324739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319945 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319945, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319980 q = 1) (hb : d324683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319980, d324683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319980, d324683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319981 q = 1) (hb : d324684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319981, d324684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319981, d324684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320036 q = 1) (hb : d324739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320036, d324739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320036, d324739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88856 (p : Pattern) (ha : d320037 p = 1) (hb : d324740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319943 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88833 q ha hb
    | true =>
      simp only [d319943, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319944 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319944, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319949 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319949, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319983 q = 1) (hb : d324686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319983, d324686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319983, d324686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319984 q = 1) (hb : d324687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d319984, d324687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319984, d324687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320037 q = 1) (hb : d324740 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320037, d324740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320037, d324740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88857 (p : Pattern) (ha : d320041 p = 1) (hb : d324744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319996 q = 1) (hb : d324699 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319996, d324699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88845 q ha hb
    | true =>
      simp only [d319996, d324699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d319997 q = 1) (hb : d324700 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319997, d324700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319997, d324700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319939 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88832 q ha hb
    | true =>
      simp only [d319939, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319940 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319940, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319998 q = 1) (hb : d324701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d319998, d324701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319998, d324701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319999 q = 1) (hb : d324702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d319999, d324702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319999, d324702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320000 q = 1) (hb : d324703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320000, d324703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320000, d324703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320041 q = 1) (hb : d324744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320041, d324744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320041, d324744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88858 (p : Pattern) (ha : d320044 p = 1) (hb : d324747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320018 q = 1) (hb : d324721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320018, d324721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88850 q ha hb
    | true =>
      simp only [d320018, d324721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320019 q = 1) (hb : d324722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320019, d324722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320019, d324722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320020 q = 1) (hb : d324723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320020, d324723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320020, d324723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320021 q = 1) (hb : d324724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320021, d324724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320021, d324724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320022 q = 1) (hb : d324725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320022, d324725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320022, d324725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320044 q = 1) (hb : d324747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320044, d324747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320044, d324747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88859 (p : Pattern) (ha : d320050 p = 1) (hb : d324753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319976 q = 1) (hb : d324679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319976, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88840 q ha hb
    | true =>
      simp only [d319976, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88841 q ha hb
  have h2 (q : Pattern) (ha : d319977 q = 1) (hb : d324680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319977, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319977, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319978 q = 1) (hb : d324681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319978, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319978, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319979 q = 1) (hb : d324682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319979, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319979, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319986 q = 1) (hb : d324689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319986, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88842 q ha hb
    | true =>
      simp only [d319986, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88843 q ha hb
  have h6 (q : Pattern) (ha : d319987 q = 1) (hb : d324690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319987, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319987, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319988 q = 1) (hb : d324691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319988, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319988, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320002 q = 1) (hb : d324705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320002, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88846 q ha hb
    | true =>
      simp only [d320002, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319953 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d320003 q = 1) (hb : d324706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320003, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320003, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d320024 q = 1) (hb : d324727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320024, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88851 q ha hb
    | true =>
      simp only [d320024, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320025 q = 1) (hb : d324728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320025, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320025, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d320026 q = 1) (hb : d324729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320026, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320026, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320027 q = 1) (hb : d324730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320027, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320027, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320028 q = 1) (hb : d324731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320028, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320028, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320032 q = 1) (hb : d324735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320032, d324735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88853 q ha hb
    | true =>
      simp only [d320032, d324735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88854 q ha hb
  have h17 (q : Pattern) (ha : d320033 q = 1) (hb : d324736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320033, d324736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320033, d324736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d320034 q = 1) (hb : d324737 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320034, d324737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320034, d324737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d320035 q = 1) (hb : d324738 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320035, d324738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320035, d324738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d320038 q = 1) (hb : d324741 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320038, d324741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88855 q ha hb
    | true =>
      simp only [d320038, d324741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88856 q ha hb
  have h21 (q : Pattern) (ha : d320039 q = 1) (hb : d324742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320039, d324742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320039, d324742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d320040 q = 1) (hb : d324743 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320040, d324743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d320040, d324743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d320042 q = 1) (hb : d324745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320042, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88857 q ha hb
    | true =>
      simp only [d320042, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88837 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d319963 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d320043 q = 1) (hb : d324746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320043, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d320043, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d320045 q = 1) (hb : d324748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320045, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88858 q ha hb
    | true =>
      simp only [d320045, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d320046 q = 1) (hb : d324749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320046, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d320046, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d320047 q = 1) (hb : d324750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320047, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d320047, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d320048 q = 1) (hb : d324751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320048, d324751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d320048, d324751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d320049 q = 1) (hb : d324752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320049, d324752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d320049, d324752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d320050 q = 1) (hb : d324753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320050, d324753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320050, d324753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro88860 (p : Pattern) (ha : d320057 p = 1) (hb : d324760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319953 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
    | true =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
  have h2 (q : Pattern) (ha : d319954 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319954, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319954, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319955 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319955, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319955, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d319956 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319956, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319956, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319957 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319957, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319957, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320052 q = 1) (hb : d324755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320052, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
    | true =>
      simp only [d320052, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320053 q = 1) (hb : d324756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320053, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320053, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320054 q = 1) (hb : d324757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320054, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320054, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320055 q = 1) (hb : d324758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320055, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320055, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320056 q = 1) (hb : d324759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320056, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320056, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320057 q = 1) (hb : d324760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320057, d324760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320057, d324760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88861 (p : Pattern) (ha : d320063 p = 1) (hb : d324766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320052 q = 1) (hb : d324755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320052, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
    | true =>
      simp only [d320052, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320053 q = 1) (hb : d324756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320053, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320053, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320054 q = 1) (hb : d324757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320054, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320054, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320055 q = 1) (hb : d324758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320055, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320055, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320056 q = 1) (hb : d324759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320056, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320056, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320058 q = 1) (hb : d324761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320058, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88838 q ha hb
    | true =>
      simp only [d320058, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320059 q = 1) (hb : d324762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320059, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320059, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320060 q = 1) (hb : d324763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320060, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320060, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320061 q = 1) (hb : d324764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320061, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320061, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320062 q = 1) (hb : d324765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320062, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320062, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320063 q = 1) (hb : d324766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320063, d324766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320063, d324766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro88862 (p : Pattern) (ha : d320070 p = 1) (hb : d324773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320042 q = 1) (hb : d324745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320042, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88857 q ha hb
    | true =>
      simp only [d320042, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88837 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319963 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320043 q = 1) (hb : d324746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320043, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320043, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d320045 q = 1) (hb : d324748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320045, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88858 q ha hb
    | true =>
      simp only [d320045, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320046 q = 1) (hb : d324749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320046, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320046, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320047 q = 1) (hb : d324750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320047, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320047, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320068 q = 1) (hb : d324771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320068, d324771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320068, d324771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320069 q = 1) (hb : d324772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320069, d324772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320069, d324772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320070 q = 1) (hb : d324773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320070, d324773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320070, d324773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro88863 (p : Pattern) (ha : d320072 p = 1) (hb : d324775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320058 q = 1) (hb : d324761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320058, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88838 q ha hb
    | true =>
      simp only [d320058, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320059 q = 1) (hb : d324762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320059, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320059, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320060 q = 1) (hb : d324763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320060, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320060, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320061 q = 1) (hb : d324764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320061, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320061, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320062 q = 1) (hb : d324765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320062, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320062, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320072 q = 1) (hb : d324775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320072, d324775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320072, d324775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88864 (p : Pattern) (ha : d320083 p = 1) (hb : d324786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320078 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
  have h2 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320079 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320080 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320081 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320082 q = 1) (hb : d324785 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320082, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320082, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320083 q = 1) (hb : d324786 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320083, d324786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320083, d324786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88865 (p : Pattern) (ha : d320089 p = 1) (hb : d324792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320078 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
  have h2 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320079 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320080 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320081 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320082 q = 1) (hb : d324785 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320082, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320082, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320084 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
  have h9 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d320085 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320086 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320087 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d320088 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320088, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320088, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320089 q = 1) (hb : d324792 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320089, d324792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320089, d324792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88866 (p : Pattern) (ha : d320094 p = 1) (hb : d324797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320078 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
  have h2 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320079 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320080 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320081 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320084 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
  have h8 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320085 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d320086 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d320087 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d320088 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320088, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320088, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320093 q = 1) (hb : d324796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320093, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320093, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d320094 q = 1) (hb : d324797 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320094, d324797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320094, d324797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88867 (p : Pattern) (ha : d320104 p = 1) (hb : d324802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320084 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
  have h2 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320085 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320086 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320087 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320093 q = 1) (hb : d324796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320093, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320093, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d221342 q = 1) (hb : d320099 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221342, d320099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d221342, d320099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88830 q ha hb
  have h9 (q : Pattern) (ha : d221102 q = 1) (hb : d319926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221102, d319926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88830 q ha hb
    | true =>
      simp only [d221102, d319926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d221343 q = 1) (hb : d320100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221343, d320100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d221343, d320100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d221103 q = 1) (hb : d319927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221103, d319927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d221103, d319927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d221344 q = 1) (hb : d320101 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d221344, d320101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d221344, d320101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d221345 q = 1) (hb : d320102 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d221345, d320102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d221345, d320102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d221346 q = 1) (hb : d320103 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d221346, d320103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d221346, d320103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d320104 q = 1) (hb : d324802 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320104, d324802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320104, d324802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro88868 (p : Pattern) (ha : d320110 p = 1) (hb : d324808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320090 q = 1) (hb : d324793 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320090, d324793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88864 q ha hb
    | true =>
      simp only [d320090, d324793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88865 q ha hb
  have h2 (q : Pattern) (ha : d320091 q = 1) (hb : d324794 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320091, d324794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320091, d324794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320092 q = 1) (hb : d324795 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320092, d324795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320092, d324795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320095 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320095, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88865 q ha hb
    | true =>
      simp only [d320095, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
  have h5 (q : Pattern) (ha : d320096 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320096, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320096, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320097 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320097, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320097, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320098 q = 1) (hb : d324801 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320098, d324801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320098, d324801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320105 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
    | true =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88867 q ha hb
  have h9 (q : Pattern) (ha : d320106 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320107 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320108 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320108, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320108, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d320109 q = 1) (hb : d324807 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320109, d324807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320109, d324807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320110 q = 1) (hb : d324808 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320110, d324808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320110, d324808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro88869 (p : Pattern) (ha : d320115 p = 1) (hb : d324813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320095 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320095, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88865 q ha hb
    | true =>
      simp only [d320095, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
  have h2 (q : Pattern) (ha : d320096 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320096, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320096, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320097 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320097, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320097, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320105 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
    | true =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88867 q ha hb
  have h5 (q : Pattern) (ha : d320106 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320107 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320108 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320108, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320108, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320113 q = 1) (hb : d324811 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320113, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320113, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320114 q = 1) (hb : d324812 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320114, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320114, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320115 q = 1) (hb : d324813 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320115, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320115, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro88870 (p : Pattern) (ha : d320121 p = 1) (hb : d324819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320111 q = 1) (hb : d324809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320111, d324809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88868 q ha hb
    | true =>
      simp only [d320111, d324809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320112 q = 1) (hb : d324810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320112, d324810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320112, d324810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320116 q = 1) (hb : d324814 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320116, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88869 q ha hb
    | true =>
      simp only [d320116, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320117 q = 1) (hb : d324815 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320117, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320117, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320118 q = 1) (hb : d324816 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320118, d324816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320118, d324816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320119 q = 1) (hb : d324817 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320119, d324817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320119, d324817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320120 q = 1) (hb : d324818 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320120, d324818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320120, d324818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320121 q = 1) (hb : d324819 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320121, d324819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320121, d324819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88871 (p : Pattern) (ha : d320123 p = 1) (hb : d324821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320105 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
    | true =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88867 q ha hb
  have h2 (q : Pattern) (ha : d320106 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320107 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320113 q = 1) (hb : d324811 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320113, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320113, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320122 q = 1) (hb : d324820 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320122, d324820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320122, d324820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320123 q = 1) (hb : d324821 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320123, d324821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320123, d324821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88872 (p : Pattern) (ha : d320129 p = 1) (hb : d324827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320116 q = 1) (hb : d324814 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320116, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88869 q ha hb
    | true =>
      simp only [d320116, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320117 q = 1) (hb : d324815 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320117, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320117, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320124 q = 1) (hb : d324822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320124, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88871 q ha hb
    | true =>
      simp only [d320124, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320125 q = 1) (hb : d324823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320125, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320125, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320126 q = 1) (hb : d324824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320126, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320126, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320127 q = 1) (hb : d324825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320127, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320127, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320128 q = 1) (hb : d324826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320128, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320128, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320129 q = 1) (hb : d324827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320129, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320129, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88873 (p : Pattern) (ha : d320142 p = 1) (hb : d324835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320078 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320078, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
  have h2 (q : Pattern) (ha : d319898 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88826 q ha hb
    | true =>
      simp only [d319898, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320079 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320079, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319899 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319899, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320080 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320080, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320081 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320081, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320084 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320084, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
  have h8 (q : Pattern) (ha : d319914 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88827 q ha hb
    | true =>
      simp only [d319914, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320085 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320085, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319915 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319915, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d320086 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320086, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d320087 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320087, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d320088 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320088, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320088, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320137 q = 1) (hb : d324830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320137, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320137, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88847 q ha hb
  have h15 (q : Pattern) (ha : d320005 q = 1) (hb : d324708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88847 q ha hb
    | true =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d320138 q = 1) (hb : d324831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320138, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d320138, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320006 q = 1) (hb : d324709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d320139 q = 1) (hb : d324832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320139, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320139, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d320140 q = 1) (hb : d324833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320140, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d320140, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d320141 q = 1) (hb : d324834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320141, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d320141, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d320142 q = 1) (hb : d324835 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320142, d324835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320142, d324835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro88874 (p : Pattern) (ha : d320143 p = 1) (hb : d324836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320137 q = 1) (hb : d324830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320137, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320137, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88847 q ha hb
  have h2 (q : Pattern) (ha : d320005 q = 1) (hb : d324708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88847 q ha hb
    | true =>
      simp only [d320005, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320138 q = 1) (hb : d324831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320138, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320138, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320006 q = 1) (hb : d324709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320006, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320139 q = 1) (hb : d324832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320139, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320139, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320140 q = 1) (hb : d324833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320140, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320140, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d320141 q = 1) (hb : d324834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320141, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320141, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d320143 q = 1) (hb : d324836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320143, d324836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320143, d324836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro88875 (p : Pattern) (ha : d320149 p = 1) (hb : d324842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320095 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320095, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88865 q ha hb
    | true =>
      simp only [d320095, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
  have h2 (q : Pattern) (ha : d320096 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320096, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320096, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320097 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320097, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320097, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320105 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88866 q ha hb
    | true =>
      simp only [d320105, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88867 q ha hb
  have h5 (q : Pattern) (ha : d320106 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320106, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320107 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320107, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320108 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320108, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320108, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320144 q = 1) (hb : d324837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320144, d324837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88873 q ha hb
    | true =>
      simp only [d320144, d324837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88874 q ha hb
  have h9 (q : Pattern) (ha : d320145 q = 1) (hb : d324838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320145, d324838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320145, d324838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320146 q = 1) (hb : d324839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320146, d324839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320146, d324839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320147 q = 1) (hb : d324840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320147, d324840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320147, d324840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320148 q = 1) (hb : d324841 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320148, d324841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320148, d324841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320149 q = 1) (hb : d324842 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320149, d324842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320149, d324842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro88876 (p : Pattern) (ha : d320155 p = 1) (hb : d324848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320150 q = 1) (hb : d324843 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320150, d324843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88875 q ha hb
    | true =>
      simp only [d320150, d324843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320151 q = 1) (hb : d324844 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320151, d324844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320151, d324844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320152 q = 1) (hb : d324845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320152, d324845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320152, d324845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320153 q = 1) (hb : d324846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320153, d324846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320153, d324846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320154 q = 1) (hb : d324847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320154, d324847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320154, d324847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320155 q = 1) (hb : d324848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320155, d324848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320155, d324848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88877 (p : Pattern) (ha : d320161 p = 1) (hb : d324854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320130 q = 1) (hb : d324828 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320130, d324828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88870 q ha hb
    | true =>
      simp only [d320130, d324828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88872 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320135 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320136 q = 1) (hb : d324829 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320136, d324829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320136, d324829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d320156 q = 1) (hb : d324849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320156, d324849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88876 q ha hb
    | true =>
      simp only [d320156, d324849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320157 q = 1) (hb : d324850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320157, d324850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320157, d324850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320158 q = 1) (hb : d324851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320158, d324851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320158, d324851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320159 q = 1) (hb : d324852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320159, d324852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320159, d324852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320160 q = 1) (hb : d324853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320160, d324853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320160, d324853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320161 q = 1) (hb : d324854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320161, d324854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320161, d324854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro88878 (p : Pattern) (ha : d320134 p = 1) (hb : d324859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320124 q = 1) (hb : d324822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320124, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88871 q ha hb
    | true =>
      simp only [d320124, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320125 q = 1) (hb : d324823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320125, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320125, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320131 q = 1) (hb : d324856 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320131, d324856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320131, d324856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320132 q = 1) (hb : d324857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320132, d324857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320132, d324857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320133 q = 1) (hb : d324858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320133, d324858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320133, d324858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320134 q = 1) (hb : d324859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320134, d324859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320134, d324859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88879 (p : Pattern) (ha : d320168 p = 1) (hb : d324865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320163 q = 1) (hb : d324860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320163, d324860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88878 q ha hb
    | true =>
      simp only [d320163, d324860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320164 q = 1) (hb : d324861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320164, d324861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320164, d324861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320165 q = 1) (hb : d324862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320165, d324862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320165, d324862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320166 q = 1) (hb : d324863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320166, d324863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320166, d324863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320167 q = 1) (hb : d324864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320167, d324864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320167, d324864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320168 q = 1) (hb : d324865 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320168, d324865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320168, d324865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88880 (p : Pattern) (ha : d320174 p = 1) (hb : d324871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319959 q = 1) (hb : d324662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319959, d324662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319959, d324662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88836 q ha hb
  have h2 (q : Pattern) (ha : d319960 q = 1) (hb : d324663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319960, d324663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319960, d324663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d319969 q = 1) (hb : d324672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319969, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88836 q ha hb
    | true =>
      simp only [d319969, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88839 q ha hb
  have h4 (q : Pattern) (ha : d319970 q = 1) (hb : d324673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319970, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319970, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d319971 q = 1) (hb : d324674 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319971, d324674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d319971, d324674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320051 q = 1) (hb : d324754 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320051, d324754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88852 q ha hb
    | true =>
      simp only [d320051, d324754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88859 q ha hb
  have h7 (q : Pattern) (ha : d320064 q = 1) (hb : d324767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320064, d324767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88860 q ha hb
    | true =>
      simp only [d320064, d324767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88861 q ha hb
  have h8 (q : Pattern) (ha : d320065 q = 1) (hb : d324768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320065, d324768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320065, d324768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320066 q = 1) (hb : d324769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320066, d324769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320066, d324769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d320067 q = 1) (hb : d324770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320067, d324770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320067, d324770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320071 q = 1) (hb : d324774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320071, d324774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320071, d324774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88862 q ha hb
  have h12 (q : Pattern) (ha : d320073 q = 1) (hb : d324776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320073, d324776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320073, d324776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88863 q ha hb
  have h13 (q : Pattern) (ha : d320074 q = 1) (hb : d324777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320074, d324777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320074, d324777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320075 q = 1) (hb : d324778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320075, d324778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320075, d324778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d320076 q = 1) (hb : d324779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320076, d324779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d320076, d324779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d320077 q = 1) (hb : d324780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320077, d324780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320077, d324780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320162 q = 1) (hb : d324855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320162, d324855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320162, d324855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88877 q ha hb
  have h18 (q : Pattern) (ha : d320169 q = 1) (hb : d324866 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320169, d324866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320169, d324866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88879 q ha hb
  have h19 (q : Pattern) (ha : d320170 q = 1) (hb : d324867 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320170, d324867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320170, d324867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d320171 q = 1) (hb : d324868 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320171, d324868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d320171, d324868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d320172 q = 1) (hb : d324869 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320172, d324869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d320172, d324869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d320173 q = 1) (hb : d324870 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320173, d324870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d320173, d324870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d320174 q = 1) (hb : d324871 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d320174, d324871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320174, d324871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro88881 (p : Pattern) (ha : d320180 p = 1) (hb : d324877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320175 q = 1) (hb : d324872 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d320175, d324872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320175, d324872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88880 q ha hb
  have h2 (q : Pattern) (ha : d320176 q = 1) (hb : d324873 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d320176, d324873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320176, d324873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320177 q = 1) (hb : d324874 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d320177, d324874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320177, d324874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320178 q = 1) (hb : d324875 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d320178, d324875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320178, d324875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320179 q = 1) (hb : d324876 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d320179, d324876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320179, d324876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320180 q = 1) (hb : d324877 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d320180, d324877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320180, d324877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88882 (p : Pattern) (ha : d320471 p = 1) (hb : d326423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d325771 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d325771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88661 q ha hb
    | true =>
      simp only [d319211, d325771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88708 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d326044 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d326044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d326044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88763 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d326045 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d326045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d326045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d326418 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d326418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d326418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88825 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d326419 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d326419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d326419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d326420 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d326420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d326420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d324878 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d324878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d324878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88881 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d324879 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d324879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d324879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d324880 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d324880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d324880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d326421 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d326421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d326421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320466 q = 1) (hb : d321721 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320466, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320466, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86284 q ha hb
  have h12 (q : Pattern) (ha : d320467 q = 1) (hb : d321722 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320467, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320467, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320468 q = 1) (hb : d321723 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320468, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320468, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320469 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320469, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320469, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320470 q = 1) (hb : d326422 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d326422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d326422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320471 q = 1) (hb : d326423 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d326423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320471, d326423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro88883 (p : Pattern) (ha : d320477 p = 1) (hb : d326429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d326424 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d326424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88882 q ha hb
    | true =>
      simp only [d320472, d326424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d326425 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d326425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d326425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d326426 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d326426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d326426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d326427 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d326427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d326427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d326428 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d326428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d326428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d326429 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d326429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d326429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88884 (p : Pattern) (ha : d320483 p = 1) (hb : d326435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d326430 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88883 q ha hb
    | true =>
      simp only [d320478, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d326431 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d326432 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d326433 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d326434 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d326435 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88885 (p : Pattern) (ha : d320489 p = 1) (hb : d326441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d326436 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88884 q ha hb
    | true =>
      simp only [d320484, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d326437 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d326438 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d326439 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d326440 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d326441 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88886 (p : Pattern) (ha : d320495 p = 1) (hb : d326447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d326442 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88885 q ha hb
    | true =>
      simp only [d320490, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d326443 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d326444 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d326445 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d326446 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d326447 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88887 (p : Pattern) (ha : d320501 p = 1) (hb : d326453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d326448 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88886 q ha hb
    | true =>
      simp only [d320496, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d326449 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d326450 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d326451 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d326452 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d326453 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88888 (p : Pattern) (ha : d320507 p = 1) (hb : d326459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d326454 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88887 q ha hb
    | true =>
      simp only [d320502, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d326455 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d326456 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d326457 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d326458 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d326459 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88889 (p : Pattern) (ha : d320513 p = 1) (hb : d326465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d326460 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88888 q ha hb
    | true =>
      simp only [d320508, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d326461 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d326462 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d326463 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d326464 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d326465 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88890 (p : Pattern) (ha : d270853 p = 1) (hb : d325306 p = 1) : d326468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d325306 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36033 q = 1) (hb : d325306 q = 1) : d325339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88265 q ha hb
    | true =>
      simp only [d36033, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36093 q = 1) (hb : d325306 q = 1) : d325399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36093, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36094 q = 1) (hb : d325306 q = 1) : d325400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36094, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36095 q = 1) (hb : d325306 q = 1) : d325401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36096 q = 1) (hb : d325306 q = 1) : d325402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270853 q = 1) (hb : d325306 q = 1) : d326468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270853, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270853, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro88891 (p : Pattern) (ha : d270863 p = 1) (hb : d325306 p = 1) : d326478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d325306 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36069 q = 1) (hb : d325306 q = 1) : d325375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36069, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88270 q ha hb
    | true =>
      simp only [d36069, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270859 q = 1) (hb : d325306 q = 1) : d326474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270859, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270859, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270860 q = 1) (hb : d325306 q = 1) : d326475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270860, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270860, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d270861 q = 1) (hb : d325306 q = 1) : d326476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270861, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270861, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270862 q = 1) (hb : d325306 q = 1) : d326477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270862, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270862, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270863 q = 1) (hb : d325306 q = 1) : d326478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270863, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270863, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro88892 (p : Pattern) (ha : d270869 p = 1) (hb : d325306 p = 1) : d326484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36098 q = 1) (hb : d325306 q = 1) : d325404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88273 q ha hb
    | true =>
      simp only [d36098, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88274 q ha hb
  have h2 (q : Pattern) (ha : d36099 q = 1) (hb : d325306 q = 1) : d325405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36099, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270851 q = 1) (hb : d325306 q = 1) : d326466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270851, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270851, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270852 q = 1) (hb : d325306 q = 1) : d326467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270852, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270852, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270854 q = 1) (hb : d325306 q = 1) : d326469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270854, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270854, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88890 q ha hb
  have h6 (q : Pattern) (ha : d270855 q = 1) (hb : d325306 q = 1) : d326470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270855, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270855, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270856 q = 1) (hb : d325306 q = 1) : d326471 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270856, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270856, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270857 q = 1) (hb : d325306 q = 1) : d326472 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270857, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270857, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270858 q = 1) (hb : d325306 q = 1) : d326473 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270858, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270858, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270864 q = 1) (hb : d325306 q = 1) : d326479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270864, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270864, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88891 q ha hb
  have h11 (q : Pattern) (ha : d270865 q = 1) (hb : d325306 q = 1) : d326480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270865, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270865, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270866 q = 1) (hb : d325306 q = 1) : d326481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270866, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270866, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270867 q = 1) (hb : d325306 q = 1) : d326482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270867, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270867, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270868 q = 1) (hb : d325306 q = 1) : d326483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270868, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270868, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270869 q = 1) (hb : d325306 q = 1) : d326484 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270869, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270869, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88893 (p : Pattern) (ha : d270875 p = 1) (hb : d325306 p = 1) : d326490 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d325306 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270870 q = 1) (hb : d325306 q = 1) : d326485 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270870, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270870, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88892 q ha hb
  have h3 (q : Pattern) (ha : d270871 q = 1) (hb : d325306 q = 1) : d326486 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270871, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270871, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270872 q = 1) (hb : d325306 q = 1) : d326487 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270872, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270872, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270873 q = 1) (hb : d325306 q = 1) : d326488 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270873, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270873, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270874 q = 1) (hb : d325306 q = 1) : d326489 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270874, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270874, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270875 q = 1) (hb : d325306 q = 1) : d326490 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270875, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270875, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro88894 (p : Pattern) (ha : d270878 p = 1) (hb : d325306 p = 1) : d326493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36307 q = 1) (hb : d325306 q = 1) : d325568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88304 q ha hb
    | true =>
      simp only [d36307, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88305 q ha hb
  have h2 (q : Pattern) (ha : d36308 q = 1) (hb : d325306 q = 1) : d325569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36308, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36309 q = 1) (hb : d325306 q = 1) : d325570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36309, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36310 q = 1) (hb : d325306 q = 1) : d325571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36311 q = 1) (hb : d325306 q = 1) : d325572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270878 q = 1) (hb : d325306 q = 1) : d326493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270878, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270878, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88895 (p : Pattern) (ha : d270889 p = 1) (hb : d325306 p = 1) : d326504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270884 q = 1) (hb : d325306 q = 1) : d326499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270884, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88340 q ha hb
    | true =>
      simp only [d270884, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88311 q ha hb
  have h2 (q : Pattern) (ha : d270885 q = 1) (hb : d325306 q = 1) : d326500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270885, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270885, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270886 q = 1) (hb : d325306 q = 1) : d326501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270886, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270886, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270887 q = 1) (hb : d325306 q = 1) : d326502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270887, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270887, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270888 q = 1) (hb : d325306 q = 1) : d326503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270888, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270888, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270889 q = 1) (hb : d325306 q = 1) : d326504 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270889, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270889, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88896 (p : Pattern) (ha : d270895 p = 1) (hb : d325306 p = 1) : d326510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36313 q = 1) (hb : d325306 q = 1) : d325574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88303 q ha hb
    | true =>
      simp only [d36313, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88306 q ha hb
  have h2 (q : Pattern) (ha : d36314 q = 1) (hb : d325306 q = 1) : d325575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36314, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270876 q = 1) (hb : d325306 q = 1) : d326491 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270876, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270876, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270877 q = 1) (hb : d325306 q = 1) : d326492 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270877, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270877, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270879 q = 1) (hb : d325306 q = 1) : d326494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270879, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270879, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88894 q ha hb
  have h6 (q : Pattern) (ha : d270880 q = 1) (hb : d325306 q = 1) : d326495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270880, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270880, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270881 q = 1) (hb : d325306 q = 1) : d326496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270881, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270881, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270882 q = 1) (hb : d325306 q = 1) : d326497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270882, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270882, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270883 q = 1) (hb : d325306 q = 1) : d326498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270883, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270883, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270890 q = 1) (hb : d325306 q = 1) : d326505 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270890, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270890, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88895 q ha hb
  have h11 (q : Pattern) (ha : d270891 q = 1) (hb : d325306 q = 1) : d326506 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270891, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270891, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270892 q = 1) (hb : d325306 q = 1) : d326507 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270892, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270892, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270893 q = 1) (hb : d325306 q = 1) : d326508 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270893, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270893, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270894 q = 1) (hb : d325306 q = 1) : d326509 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270894, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270894, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270895 q = 1) (hb : d325306 q = 1) : d326510 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270895, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270895, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88897 (p : Pattern) (ha : d270901 p = 1) (hb : d325306 p = 1) : d326516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270896 q = 1) (hb : d325306 q = 1) : d326511 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270896, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270896, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88896 q ha hb
  have h2 (q : Pattern) (ha : d270897 q = 1) (hb : d325306 q = 1) : d326512 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270897, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270897, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270898 q = 1) (hb : d325306 q = 1) : d326513 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270898, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270898, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270899 q = 1) (hb : d325306 q = 1) : d326514 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270899, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270899, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270900 q = 1) (hb : d325306 q = 1) : d326515 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270900, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270900, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270901 q = 1) (hb : d325306 q = 1) : d326516 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270901, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270901, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88898 (p : Pattern) (ha : d270905 p = 1) (hb : d325306 p = 1) : d326520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36639 q = 1) (hb : d325306 q = 1) : d325817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88354 q ha hb
    | true =>
      simp only [d36639, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88355 q ha hb
  have h2 (q : Pattern) (ha : d36640 q = 1) (hb : d325306 q = 1) : d325818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36640, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36641 q = 1) (hb : d325306 q = 1) : d325819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36641, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36642 q = 1) (hb : d325306 q = 1) : d325820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36643 q = 1) (hb : d325306 q = 1) : d325821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270905 q = 1) (hb : d325306 q = 1) : d326520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270905, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270905, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88899 (p : Pattern) (ha : d270916 p = 1) (hb : d325306 p = 1) : d326531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270911 q = 1) (hb : d325306 q = 1) : d326526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270911, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88394 q ha hb
    | true =>
      simp only [d270911, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88363 q ha hb
  have h2 (q : Pattern) (ha : d270912 q = 1) (hb : d325306 q = 1) : d326527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270912, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270912, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270913 q = 1) (hb : d325306 q = 1) : d326528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270913, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270913, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270914 q = 1) (hb : d325306 q = 1) : d326529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270914, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270914, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270915 q = 1) (hb : d325306 q = 1) : d326530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270915, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270915, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270916 q = 1) (hb : d325306 q = 1) : d326531 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270916, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270916, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88900 (p : Pattern) (ha : d270922 p = 1) (hb : d325306 p = 1) : d326537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36645 q = 1) (hb : d325306 q = 1) : d325823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36645, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88353 q ha hb
    | true =>
      simp only [d36645, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88356 q ha hb
  have h2 (q : Pattern) (ha : d36646 q = 1) (hb : d325306 q = 1) : d325824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36646, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36646, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270903 q = 1) (hb : d325306 q = 1) : d326518 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270903, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270903, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270904 q = 1) (hb : d325306 q = 1) : d326519 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270904, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270904, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270906 q = 1) (hb : d325306 q = 1) : d326521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270906, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270906, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88898 q ha hb
  have h6 (q : Pattern) (ha : d270907 q = 1) (hb : d325306 q = 1) : d326522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270907, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270907, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270908 q = 1) (hb : d325306 q = 1) : d326523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270908, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270908, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270909 q = 1) (hb : d325306 q = 1) : d326524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270909, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270909, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270910 q = 1) (hb : d325306 q = 1) : d326525 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270910, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270910, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270917 q = 1) (hb : d325306 q = 1) : d326532 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270917, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270917, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88899 q ha hb
  have h11 (q : Pattern) (ha : d270918 q = 1) (hb : d325306 q = 1) : d326533 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270918, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270918, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270919 q = 1) (hb : d325306 q = 1) : d326534 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270919, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270919, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270920 q = 1) (hb : d325306 q = 1) : d326535 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270920, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270920, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270921 q = 1) (hb : d325306 q = 1) : d326536 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270921, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270921, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270922 q = 1) (hb : d325306 q = 1) : d326537 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270922, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270922, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88901 (p : Pattern) (ha : d270928 p = 1) (hb : d325306 p = 1) : d326543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270923 q = 1) (hb : d325306 q = 1) : d326538 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270923, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270923, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88900 q ha hb
  have h2 (q : Pattern) (ha : d270924 q = 1) (hb : d325306 q = 1) : d326539 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270924, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270924, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270925 q = 1) (hb : d325306 q = 1) : d326540 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270925, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270925, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270926 q = 1) (hb : d325306 q = 1) : d326541 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270926, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270926, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270927 q = 1) (hb : d325306 q = 1) : d326542 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270927, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270927, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270928 q = 1) (hb : d325306 q = 1) : d326543 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270928, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270928, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88902 (p : Pattern) (ha : d270933 p = 1) (hb : d325306 p = 1) : d326548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37070 q = 1) (hb : d325306 q = 1) : d326145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88413 q ha hb
    | true =>
      simp only [d37070, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88414 q ha hb
  have h2 (q : Pattern) (ha : d37071 q = 1) (hb : d325306 q = 1) : d326146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37071, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37072 q = 1) (hb : d325306 q = 1) : d326147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37072, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37073 q = 1) (hb : d325306 q = 1) : d326148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37074 q = 1) (hb : d325306 q = 1) : d326149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270933 q = 1) (hb : d325306 q = 1) : d326548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270933, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270933, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88903 (p : Pattern) (ha : d270944 p = 1) (hb : d325306 p = 1) : d326559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270939 q = 1) (hb : d325306 q = 1) : d326554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270939, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88454 q ha hb
    | true =>
      simp only [d270939, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88422 q ha hb
  have h2 (q : Pattern) (ha : d270940 q = 1) (hb : d325306 q = 1) : d326555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270940, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270940, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270941 q = 1) (hb : d325306 q = 1) : d326556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270941, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270941, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270942 q = 1) (hb : d325306 q = 1) : d326557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270942, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270942, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270943 q = 1) (hb : d325306 q = 1) : d326558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270943, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270943, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270944 q = 1) (hb : d325306 q = 1) : d326559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270944, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270944, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88904 (p : Pattern) (ha : d270950 p = 1) (hb : d325306 p = 1) : d326565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d325306 q = 1) : d326151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88412 q ha hb
    | true =>
      simp only [d37076, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88415 q ha hb
  have h2 (q : Pattern) (ha : d37077 q = 1) (hb : d325306 q = 1) : d326152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270931 q = 1) (hb : d325306 q = 1) : d326546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270931, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270931, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270932 q = 1) (hb : d325306 q = 1) : d326547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270932, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270932, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270934 q = 1) (hb : d325306 q = 1) : d326549 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270934, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270934, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88902 q ha hb
  have h6 (q : Pattern) (ha : d270935 q = 1) (hb : d325306 q = 1) : d326550 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270935, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270935, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270936 q = 1) (hb : d325306 q = 1) : d326551 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270936, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270936, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270937 q = 1) (hb : d325306 q = 1) : d326552 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270937, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270937, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270938 q = 1) (hb : d325306 q = 1) : d326553 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270938, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270938, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270945 q = 1) (hb : d325306 q = 1) : d326560 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270945, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270945, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88903 q ha hb
  have h11 (q : Pattern) (ha : d270946 q = 1) (hb : d325306 q = 1) : d326561 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270946, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270946, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270947 q = 1) (hb : d325306 q = 1) : d326562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270947, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270947, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270948 q = 1) (hb : d325306 q = 1) : d326563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270948, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270948, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270949 q = 1) (hb : d325306 q = 1) : d326564 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270949, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270949, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270950 q = 1) (hb : d325306 q = 1) : d326565 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270950, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270950, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88905 (p : Pattern) (ha : d270956 p = 1) (hb : d325306 p = 1) : d326571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270951 q = 1) (hb : d325306 q = 1) : d326566 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270951, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270951, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88904 q ha hb
  have h2 (q : Pattern) (ha : d270952 q = 1) (hb : d325306 q = 1) : d326567 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270952, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270952, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270953 q = 1) (hb : d325306 q = 1) : d326568 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270953, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270953, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270954 q = 1) (hb : d325306 q = 1) : d326569 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270954, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270954, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270955 q = 1) (hb : d325306 q = 1) : d326570 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270955, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270955, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270956 q = 1) (hb : d325306 q = 1) : d326571 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270956, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270956, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88906 (p : Pattern) (ha : d324280 p = 1) (hb : d325306 p = 1) : d325181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37632 q = 1) (hb : d325306 q = 1) : d324666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37632, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88485 q ha hb
    | true =>
      simp only [d37632, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88486 q ha hb
  have h2 (q : Pattern) (ha : d37633 q = 1) (hb : d325306 q = 1) : d324667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37633, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37633, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37634 q = 1) (hb : d325306 q = 1) : d324668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37634, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37634, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37635 q = 1) (hb : d325306 q = 1) : d324669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37635, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37635, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37636 q = 1) (hb : d325306 q = 1) : d324670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37636, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37636, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324280 q = 1) (hb : d325306 q = 1) : d325181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324280, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324280, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88907 (p : Pattern) (ha : d324287 p = 1) (hb : d325306 p = 1) : d324813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37980 q = 1) (hb : d325306 q = 1) : d324798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37980, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88526 q ha hb
    | true =>
      simp only [d37980, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88493 q ha hb
  have h2 (q : Pattern) (ha : d37981 q = 1) (hb : d325306 q = 1) : d324799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37981, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37981, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37982 q = 1) (hb : d325306 q = 1) : d324800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37982, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37982, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d37994 q = 1) (hb : d325306 q = 1) : d324803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37994, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88493 q ha hb
    | true =>
      simp only [d37994, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88528 q ha hb
  have h5 (q : Pattern) (ha : d37995 q = 1) (hb : d325306 q = 1) : d324804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37995, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37995, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37996 q = 1) (hb : d325306 q = 1) : d324805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37996, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37996, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37997 q = 1) (hb : d325306 q = 1) : d324806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d37997, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37997, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38013 q = 1) (hb : d325306 q = 1) : d324803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38013, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88493 q ha hb
    | true =>
      simp only [d38013, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88494 q ha hb
  have h9 (q : Pattern) (ha : d38014 q = 1) (hb : d325306 q = 1) : d324804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38014, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38014, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38015 q = 1) (hb : d325306 q = 1) : d324805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38015, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38015, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38016 q = 1) (hb : d325306 q = 1) : d324811 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38016, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38016, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324286 q = 1) (hb : d325306 q = 1) : d324812 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324286, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324286, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d324287 q = 1) (hb : d325306 q = 1) : d324813 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324287, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324287, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro88908 (p : Pattern) (ha : d324293 p = 1) (hb : d325306 p = 1) : d324827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324288 q = 1) (hb : d325306 q = 1) : d324814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324288, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88907 q ha hb
    | true =>
      simp only [d324288, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324289 q = 1) (hb : d325306 q = 1) : d324815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324289, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324289, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38019 q = 1) (hb : d325306 q = 1) : d324822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38019, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88495 q ha hb
    | true =>
      simp only [d38019, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38020 q = 1) (hb : d325306 q = 1) : d324823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38020, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38020, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324290 q = 1) (hb : d325306 q = 1) : d324824 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324290, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324290, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324291 q = 1) (hb : d325306 q = 1) : d324825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324291, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324291, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324292 q = 1) (hb : d325306 q = 1) : d324826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324292, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324292, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324293 q = 1) (hb : d325306 q = 1) : d324827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324293, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324293, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro88909 (p : Pattern) (ha : d324299 p = 1) (hb : d325306 p = 1) : d325192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324294 q = 1) (hb : d325306 q = 1) : d325187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324294, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88908 q ha hb
    | true =>
      simp only [d324294, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88496 q ha hb
  have h2 (q : Pattern) (ha : d324295 q = 1) (hb : d325306 q = 1) : d325188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324295, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324295, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324296 q = 1) (hb : d325306 q = 1) : d325189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324296, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324296, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324297 q = 1) (hb : d325306 q = 1) : d325190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324297, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324297, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324298 q = 1) (hb : d325306 q = 1) : d325191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324298, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324298, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324299 q = 1) (hb : d325306 q = 1) : d325192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324299, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324299, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88910 (p : Pattern) (ha : d324305 p = 1) (hb : d325306 p = 1) : d325198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37638 q = 1) (hb : d325306 q = 1) : d324672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37638, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88484 q ha hb
    | true =>
      simp only [d37638, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88487 q ha hb
  have h2 (q : Pattern) (ha : d37639 q = 1) (hb : d325306 q = 1) : d324673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37639, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37639, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324278 q = 1) (hb : d325306 q = 1) : d325179 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324278, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324278, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324279 q = 1) (hb : d325306 q = 1) : d325180 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324279, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324279, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324281 q = 1) (hb : d325306 q = 1) : d325182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324281, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324281, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88906 q ha hb
  have h6 (q : Pattern) (ha : d324282 q = 1) (hb : d325306 q = 1) : d325183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324282, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324282, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324283 q = 1) (hb : d325306 q = 1) : d325184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324283, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324283, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324284 q = 1) (hb : d325306 q = 1) : d325185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324284, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324284, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d324285 q = 1) (hb : d325306 q = 1) : d325186 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324285, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324285, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324300 q = 1) (hb : d325306 q = 1) : d325193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324300, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324300, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88909 q ha hb
  have h11 (q : Pattern) (ha : d324301 q = 1) (hb : d325306 q = 1) : d325194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324301, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324301, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324302 q = 1) (hb : d325306 q = 1) : d325195 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324302, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324302, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d324303 q = 1) (hb : d325306 q = 1) : d325196 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324303, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324303, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d324304 q = 1) (hb : d325306 q = 1) : d325197 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324304, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324304, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d324305 q = 1) (hb : d325306 q = 1) : d325198 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324305, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324305, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88911 (p : Pattern) (ha : d324311 p = 1) (hb : d325306 p = 1) : d325204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324306 q = 1) (hb : d325306 q = 1) : d325199 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324306, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324306, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88910 q ha hb
  have h2 (q : Pattern) (ha : d324307 q = 1) (hb : d325306 q = 1) : d325200 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324307, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324307, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324308 q = 1) (hb : d325306 q = 1) : d325201 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324308, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324308, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324309 q = 1) (hb : d325306 q = 1) : d325202 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324309, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324309, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324310 q = 1) (hb : d325306 q = 1) : d325203 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324310, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324310, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324311 q = 1) (hb : d325306 q = 1) : d325204 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324311, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324311, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88912 (p : Pattern) (ha : d324318 p = 1) (hb : d325306 p = 1) : d321910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38276 q = 1) (hb : d325306 q = 1) : d46926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38276, d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88562 q ha hb
    | true =>
      simp only [d38276, d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88563 q ha hb
  have h2 (q : Pattern) (ha : d38277 q = 1) (hb : d325306 q = 1) : d46927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38277, d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38277, d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38278 q = 1) (hb : d325306 q = 1) : d46928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38278, d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38278, d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38279 q = 1) (hb : d325306 q = 1) : d46929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38279, d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38279, d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38280 q = 1) (hb : d325306 q = 1) : d46930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38280, d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38280, d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324318 q = 1) (hb : d325306 q = 1) : d321910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324318, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324318, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88913 (p : Pattern) (ha : d324325 p = 1) (hb : d325306 p = 1) : d47117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38572 q = 1) (hb : d325306 q = 1) : d47097 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38572, d47097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88600 q ha hb
    | true =>
      simp only [d38572, d47097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88570 q ha hb
  have h2 (q : Pattern) (ha : d38573 q = 1) (hb : d325306 q = 1) : d47098 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38573, d47098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38573, d47098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38574 q = 1) (hb : d325306 q = 1) : d47099 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38574, d47099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38574, d47099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38586 q = 1) (hb : d325306 q = 1) : d47107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38586, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88570 q ha hb
    | true =>
      simp only [d38586, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88602 q ha hb
  have h5 (q : Pattern) (ha : d38587 q = 1) (hb : d325306 q = 1) : d47108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38587, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38587, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38588 q = 1) (hb : d325306 q = 1) : d47109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38588, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38588, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38589 q = 1) (hb : d325306 q = 1) : d47110 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38589, d47110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38589, d47110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38605 q = 1) (hb : d325306 q = 1) : d47107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38605, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88570 q ha hb
    | true =>
      simp only [d38605, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88571 q ha hb
  have h9 (q : Pattern) (ha : d38606 q = 1) (hb : d325306 q = 1) : d47108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38606, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38606, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38607 q = 1) (hb : d325306 q = 1) : d47109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38607, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38607, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38608 q = 1) (hb : d325306 q = 1) : d47115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38608, d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38608, d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324324 q = 1) (hb : d325306 q = 1) : d47116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324324, d47116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324324, d47116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d324325 q = 1) (hb : d325306 q = 1) : d47117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324325, d47117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324325, d47117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro88914 (p : Pattern) (ha : d324331 p = 1) (hb : d325306 p = 1) : d47131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324326 q = 1) (hb : d325306 q = 1) : d47118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324326, d47118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88913 q ha hb
    | true =>
      simp only [d324326, d47118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324327 q = 1) (hb : d325306 q = 1) : d47119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324327, d47119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324327, d47119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38611 q = 1) (hb : d325306 q = 1) : d47126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38611, d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88572 q ha hb
    | true =>
      simp only [d38611, d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38612 q = 1) (hb : d325306 q = 1) : d47127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38612, d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38612, d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324328 q = 1) (hb : d325306 q = 1) : d47128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324328, d47128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324328, d47128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324329 q = 1) (hb : d325306 q = 1) : d47129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324329, d47129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324329, d47129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324330 q = 1) (hb : d325306 q = 1) : d47130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324330, d47130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324330, d47130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324331 q = 1) (hb : d325306 q = 1) : d47131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324331, d47131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324331, d47131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro88915 (p : Pattern) (ha : d324339 p = 1) (hb : d325306 p = 1) : d326581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5238 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88546 q ha hb
  have h2 (q : Pattern) (ha : d324333 q = 1) (hb : d325306 q = 1) : d324333 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d324334 q = 1) (hb : d325306 q = 1) : d326576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d324334, d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324334, d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88545 q ha hb
  have h4 (q : Pattern) (ha : d324335 q = 1) (hb : d325306 q = 1) : d326577 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d324335, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324335, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324336 q = 1) (hb : d325306 q = 1) : d326578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d324336, d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324336, d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88546 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10406 q = 1) (hb : d325306 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88545 q ha hb
    | true =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38188 q = 1) (hb : d325306 q = 1) : d46872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38188, d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38188, d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38189 q = 1) (hb : d325306 q = 1) : d46873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38189, d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38189, d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d324337 q = 1) (hb : d325306 q = 1) : d326579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d324337, d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324337, d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d324338 q = 1) (hb : d325306 q = 1) : d326580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d324338, d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324338, d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324339 q = 1) (hb : d325306 q = 1) : d326581 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d324339, d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324339, d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro88916 (p : Pattern) (ha : d324345 p = 1) (hb : d325306 p = 1) : d326587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38566 q = 1) (hb : d325306 q = 1) : d47086 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38566, d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38566, d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88551 q ha hb
  have h2 (q : Pattern) (ha : d38211 q = 1) (hb : d325306 q = 1) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38211, d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88551 q ha hb
    | true =>
      simp only [d38211, d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38567 q = 1) (hb : d325306 q = 1) : d47087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38567, d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38567, d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38212 q = 1) (hb : d325306 q = 1) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38212, d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38212, d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38568 q = 1) (hb : d325306 q = 1) : d47088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38568, d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38568, d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38569 q = 1) (hb : d325306 q = 1) : d47089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38569, d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38569, d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38603 q = 1) (hb : d325306 q = 1) : d47095 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38603, d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38603, d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38580 q = 1) (hb : d325306 q = 1) : d47101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38580, d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38580, d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88554 q ha hb
  have h9 (q : Pattern) (ha : d38234 q = 1) (hb : d325306 q = 1) : d46889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38234, d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88554 q ha hb
    | true =>
      simp only [d38234, d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d38581 q = 1) (hb : d325306 q = 1) : d47102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38581, d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38581, d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d324340 q = 1) (hb : d325306 q = 1) : d326582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d324340, d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88915 q ha hb
    | true =>
      simp only [d324340, d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324341 q = 1) (hb : d325306 q = 1) : d326583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d324341, d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324341, d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d324342 q = 1) (hb : d325306 q = 1) : d326584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d324342, d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324342, d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d324343 q = 1) (hb : d325306 q = 1) : d326585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d324343, d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324343, d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d324344 q = 1) (hb : d325306 q = 1) : d326586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d324344, d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d324344, d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d324345 q = 1) (hb : d325306 q = 1) : d326587 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324345, d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324345, d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro88917 (p : Pattern) (ha : d324351 p = 1) (hb : d325306 p = 1) : d326593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324346 q = 1) (hb : d325306 q = 1) : d326588 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d324346, d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88570 q ha hb
    | true =>
      simp only [d324346, d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88916 q ha hb
  have h2 (q : Pattern) (ha : d324347 q = 1) (hb : d325306 q = 1) : d326589 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d324347, d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324347, d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324348 q = 1) (hb : d325306 q = 1) : d326590 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d324348, d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324348, d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324349 q = 1) (hb : d325306 q = 1) : d326591 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d324349, d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324349, d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324350 q = 1) (hb : d325306 q = 1) : d326592 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324350, d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324350, d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324351 q = 1) (hb : d325306 q = 1) : d326593 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324351, d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324351, d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88918 (p : Pattern) (ha : d324357 p = 1) (hb : d325306 p = 1) : d326599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324352 q = 1) (hb : d325306 q = 1) : d326594 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324352, d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88917 q ha hb
    | true =>
      simp only [d324352, d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324353 q = 1) (hb : d325306 q = 1) : d326595 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324353, d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324353, d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324354 q = 1) (hb : d325306 q = 1) : d326596 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324354, d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324354, d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324355 q = 1) (hb : d325306 q = 1) : d326597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324355, d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324355, d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324356 q = 1) (hb : d325306 q = 1) : d326598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324356, d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324356, d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324357 q = 1) (hb : d325306 q = 1) : d326599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324357, d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324357, d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88919 (p : Pattern) (ha : d324363 p = 1) (hb : d325306 p = 1) : d326605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324358 q = 1) (hb : d325306 q = 1) : d326600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324358, d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88914 q ha hb
    | true =>
      simp only [d324358, d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88918 q ha hb
  have h2 (q : Pattern) (ha : d324359 q = 1) (hb : d325306 q = 1) : d326601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324359, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324359, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324360 q = 1) (hb : d325306 q = 1) : d326602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324360, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324360, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324361 q = 1) (hb : d325306 q = 1) : d326603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324361, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324361, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324362 q = 1) (hb : d325306 q = 1) : d326604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324362, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324362, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324363 q = 1) (hb : d325306 q = 1) : d326605 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324363, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324363, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88920 (p : Pattern) (ha : d324369 p = 1) (hb : d325306 p = 1) : d326611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38282 q = 1) (hb : d325306 q = 1) : d46932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d38282, d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88561 q ha hb
    | true =>
      simp only [d38282, d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88564 q ha hb
  have h2 (q : Pattern) (ha : d38283 q = 1) (hb : d325306 q = 1) : d46933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d38283, d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38283, d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324316 q = 1) (hb : d325306 q = 1) : d321908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324316, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324316, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324317 q = 1) (hb : d325306 q = 1) : d321909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324317, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324317, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324319 q = 1) (hb : d325306 q = 1) : d321911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324319, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324319, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88912 q ha hb
  have h6 (q : Pattern) (ha : d324320 q = 1) (hb : d325306 q = 1) : d321912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324320, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324320, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324321 q = 1) (hb : d325306 q = 1) : d321913 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324321, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324321, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324322 q = 1) (hb : d325306 q = 1) : d321914 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324322, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324322, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d324323 q = 1) (hb : d325306 q = 1) : d321915 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324323, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324323, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324364 q = 1) (hb : d325306 q = 1) : d326606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324364, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324364, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88919 q ha hb
  have h11 (q : Pattern) (ha : d324365 q = 1) (hb : d325306 q = 1) : d326607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324365, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324365, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324366 q = 1) (hb : d325306 q = 1) : d326608 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324366, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324366, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d324367 q = 1) (hb : d325306 q = 1) : d326609 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324367, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324367, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d324368 q = 1) (hb : d325306 q = 1) : d326610 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324368, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324368, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d324369 q = 1) (hb : d325306 q = 1) : d326611 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324369, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324369, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro88921 (p : Pattern) (ha : d324375 p = 1) (hb : d325306 p = 1) : d326617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324370 q = 1) (hb : d325306 q = 1) : d326612 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324370, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324370, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88920 q ha hb
  have h2 (q : Pattern) (ha : d324371 q = 1) (hb : d325306 q = 1) : d326613 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324371, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324371, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324372 q = 1) (hb : d325306 q = 1) : d326614 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324372, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324372, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324373 q = 1) (hb : d325306 q = 1) : d326615 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324373, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324373, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324374 q = 1) (hb : d325306 q = 1) : d326616 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324374, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324374, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324375 q = 1) (hb : d325306 q = 1) : d326617 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324375, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324375, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88922 (p : Pattern) (ha : d324381 p = 1) (hb : d325306 p = 1) : d326623 p = 1 := by
  have h0 (q : Pattern) (ha : d270902 q = 1) (hb : d325306 q = 1) : d326517 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270902, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88893 q ha hb
    | true =>
      simp only [d270902, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88897 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270929 q = 1) (hb : d325306 q = 1) : d326544 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270929, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270929, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88901 q ha hb
  have h3 (q : Pattern) (ha : d270930 q = 1) (hb : d325306 q = 1) : d326545 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270930, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270930, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270957 q = 1) (hb : d325306 q = 1) : d326572 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270957, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270957, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88905 q ha hb
  have h5 (q : Pattern) (ha : d270958 q = 1) (hb : d325306 q = 1) : d326573 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270958, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270958, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270959 q = 1) (hb : d325306 q = 1) : d326574 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270959, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270959, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d324312 q = 1) (hb : d325306 q = 1) : d325205 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324312, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324312, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88911 q ha hb
  have h8 (q : Pattern) (ha : d324313 q = 1) (hb : d325306 q = 1) : d325206 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324313, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324313, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d324314 q = 1) (hb : d325306 q = 1) : d325207 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324314, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324314, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324315 q = 1) (hb : d325306 q = 1) : d326575 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324315, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324315, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d324376 q = 1) (hb : d325306 q = 1) : d326618 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324376, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324376, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88921 q ha hb
  have h12 (q : Pattern) (ha : d324377 q = 1) (hb : d325306 q = 1) : d326619 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324377, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324377, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d324378 q = 1) (hb : d325306 q = 1) : d326620 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324378, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324378, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d324379 q = 1) (hb : d325306 q = 1) : d326621 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324379, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324379, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d324380 q = 1) (hb : d325306 q = 1) : d326622 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d324380, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324380, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d324381 q = 1) (hb : d325306 q = 1) : d326623 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d324381, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d324381, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro88923 (p : Pattern) (ha : d324387 p = 1) (hb : d325306 p = 1) : d326629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324382 q = 1) (hb : d325306 q = 1) : d326624 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d324382, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88922 q ha hb
    | true =>
      simp only [d324382, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324383 q = 1) (hb : d325306 q = 1) : d326625 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d324383, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324383, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324384 q = 1) (hb : d325306 q = 1) : d326626 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d324384, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324384, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324385 q = 1) (hb : d325306 q = 1) : d326627 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d324385, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324385, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324386 q = 1) (hb : d325306 q = 1) : d326628 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d324386, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324386, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324387 q = 1) (hb : d325306 q = 1) : d326629 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d324387, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324387, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88924 (p : Pattern) (ha : d324393 p = 1) (hb : d325306 p = 1) : d326635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324388 q = 1) (hb : d325306 q = 1) : d326630 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d324388, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88923 q ha hb
    | true =>
      simp only [d324388, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324389 q = 1) (hb : d325306 q = 1) : d326631 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d324389, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324389, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324390 q = 1) (hb : d325306 q = 1) : d326632 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d324390, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324390, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324391 q = 1) (hb : d325306 q = 1) : d326633 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d324391, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324391, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324392 q = 1) (hb : d325306 q = 1) : d326634 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d324392, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324392, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324393 q = 1) (hb : d325306 q = 1) : d326635 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d324393, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324393, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88925 (p : Pattern) (ha : d324399 p = 1) (hb : d325306 p = 1) : d326641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324394 q = 1) (hb : d325306 q = 1) : d326636 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d324394, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88924 q ha hb
    | true =>
      simp only [d324394, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324395 q = 1) (hb : d325306 q = 1) : d326637 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d324395, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324395, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324396 q = 1) (hb : d325306 q = 1) : d326638 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d324396, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324396, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324397 q = 1) (hb : d325306 q = 1) : d326639 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d324397, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324397, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324398 q = 1) (hb : d325306 q = 1) : d326640 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d324398, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324398, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324399 q = 1) (hb : d325306 q = 1) : d326641 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d324399, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324399, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88926 (p : Pattern) (ha : d324405 p = 1) (hb : d325306 p = 1) : d326647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324400 q = 1) (hb : d325306 q = 1) : d326642 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d324400, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88925 q ha hb
    | true =>
      simp only [d324400, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324401 q = 1) (hb : d325306 q = 1) : d326643 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d324401, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324401, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324402 q = 1) (hb : d325306 q = 1) : d326644 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d324402, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324402, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324403 q = 1) (hb : d325306 q = 1) : d326645 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d324403, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324403, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324404 q = 1) (hb : d325306 q = 1) : d326646 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d324404, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324404, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324405 q = 1) (hb : d325306 q = 1) : d326647 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d324405, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324405, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88927 (p : Pattern) (ha : d324411 p = 1) (hb : d325306 p = 1) : d326653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324406 q = 1) (hb : d325306 q = 1) : d326648 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d324406, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88926 q ha hb
    | true =>
      simp only [d324406, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324407 q = 1) (hb : d325306 q = 1) : d326649 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d324407, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324407, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324408 q = 1) (hb : d325306 q = 1) : d326650 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d324408, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324408, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324409 q = 1) (hb : d325306 q = 1) : d326651 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d324409, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324409, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324410 q = 1) (hb : d325306 q = 1) : d326652 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d324410, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324410, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324411 q = 1) (hb : d325306 q = 1) : d326653 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d324411, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324411, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88928 (p : Pattern) (ha : d324417 p = 1) (hb : d325306 p = 1) : d326659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324412 q = 1) (hb : d325306 q = 1) : d326654 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d324412, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88927 q ha hb
    | true =>
      simp only [d324412, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324413 q = 1) (hb : d325306 q = 1) : d326655 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d324413, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324413, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324414 q = 1) (hb : d325306 q = 1) : d326656 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d324414, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324414, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324415 q = 1) (hb : d325306 q = 1) : d326657 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d324415, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324415, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324416 q = 1) (hb : d325306 q = 1) : d326658 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d324416, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324416, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324417 q = 1) (hb : d325306 q = 1) : d326659 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d324417, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324417, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88929 (p : Pattern) (ha : d324423 p = 1) (hb : d325306 p = 1) : d326665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324418 q = 1) (hb : d325306 q = 1) : d326660 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d324418, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88928 q ha hb
    | true =>
      simp only [d324418, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324419 q = 1) (hb : d325306 q = 1) : d326661 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d324419, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324419, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324420 q = 1) (hb : d325306 q = 1) : d326662 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d324420, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324420, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324421 q = 1) (hb : d325306 q = 1) : d326663 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d324421, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324421, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324422 q = 1) (hb : d325306 q = 1) : d326664 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d324422, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324422, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324423 q = 1) (hb : d325306 q = 1) : d326665 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d324423, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324423, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro88930 (p : Pattern) (ha : d318887 p = 1) (hb : d325396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d318754 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318754, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88626 q ha hb
    | true =>
      simp only [d318754, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d318877 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318877, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d318877, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d318884 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318884, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318884, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d318885 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318885, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d318885, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318886 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318886, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318886, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318887 q = 1) (hb : d325396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318887, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318887, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88931 (p : Pattern) (ha : d318906 p = 1) (hb : d325403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318754 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318754, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88626 q ha hb
    | true =>
      simp only [d318754, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d318877 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318877, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d318877, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d318884 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318884, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318884, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d318885 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318885, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318885, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318886 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318886, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318886, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318892 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d318896 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d318761 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318761, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88628 q ha hb
    | true =>
      simp only [d318761, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d318899 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318899, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d318899, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318903 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318903, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318903, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d318904 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318904, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d318904, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d318905 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318905, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d318905, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d318906 q = 1) (hb : d325403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318906, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318906, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88932 (p : Pattern) (ha : d318915 p = 1) (hb : d326468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318761 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318761, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88628 q ha hb
    | true =>
      simp only [d318761, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d318899 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318899, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318899, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318903 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318903, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318903, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318913 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318913, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318913, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318914 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318914, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318914, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318915 q = 1) (hb : d326468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318915, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318915, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88933 (p : Pattern) (ha : d318955 p = 1) (hb : d326478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318797 q = 1) (hb : d325375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318797, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88633 q ha hb
    | true =>
      simp only [d318797, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d318945 q = 1) (hb : d326474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318945, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318945, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318951 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318952 q = 1) (hb : d326475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318952, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318952, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318953 q = 1) (hb : d326476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318953, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318953, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318954 q = 1) (hb : d326477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318954, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318954, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318955 q = 1) (hb : d326478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318955, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318955, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88934 (p : Pattern) (ha : d318961 p = 1) (hb : d326484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318828 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318907 q = 1) (hb : d325404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318907, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88930 q ha hb
    | true =>
      simp only [d318907, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88931 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318910 q = 1) (hb : d325405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318910, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318910, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318911 q = 1) (hb : d326466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318911, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318911, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318912 q = 1) (hb : d326467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318912, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318912, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318916 q = 1) (hb : d326469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318916, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318916, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88932 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d318917 q = 1) (hb : d326470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318917, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318917, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d318918 q = 1) (hb : d326471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318918, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318918, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d318919 q = 1) (hb : d326472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318919, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318919, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d318920 q = 1) (hb : d326473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318920, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318920, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318956 q = 1) (hb : d326479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318956, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318956, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88933 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318957 q = 1) (hb : d326480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318957, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318957, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d318958 q = 1) (hb : d326481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318958, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318958, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d318959 q = 1) (hb : d326482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318959, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318959, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d318960 q = 1) (hb : d326483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318960, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318960, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d318961 q = 1) (hb : d326484 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318961, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318961, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88935 (p : Pattern) (ha : d318967 p = 1) (hb : d326490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d318809 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86335 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d318810 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d318811 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d318812 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d318813 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318962 q = 1) (hb : d326485 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318962, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318962, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88934 q ha hb
  have h8 (q : Pattern) (ha : d318963 q = 1) (hb : d326486 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318963, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318963, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318964 q = 1) (hb : d326487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318964, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318964, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318965 q = 1) (hb : d326488 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318965, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318965, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318966 q = 1) (hb : d326489 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318966, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318966, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318967 q = 1) (hb : d326490 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318967, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d318967, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro88936 (p : Pattern) (ha : d319082 p = 1) (hb : d325563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d318985 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318985, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88664 q ha hb
    | true =>
      simp only [d318985, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88665 q ha hb
  have h5 (q : Pattern) (ha : d319072 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319072, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319072, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d319079 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319079, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319079, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d319080 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319080, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319080, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319081 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319081, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319081, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319082 q = 1) (hb : d325563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319082, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319082, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88937 (p : Pattern) (ha : d319103 p = 1) (hb : d325573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318985 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318985, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88664 q ha hb
    | true =>
      simp only [d318985, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88665 q ha hb
  have h4 (q : Pattern) (ha : d319072 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319072, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319072, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d319079 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319079, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319079, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319080 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319080, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319080, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319081 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319081, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319081, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319088 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319093 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d318995 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318995, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88667 q ha hb
    | true =>
      simp only [d318995, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88668 q ha hb
  have h13 (q : Pattern) (ha : d319096 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319096, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319096, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319100 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319100, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319100, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319101 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319101, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d319101, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319102 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319102, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d319102, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319103 q = 1) (hb : d325573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319103, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319103, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88938 (p : Pattern) (ha : d319123 p = 1) (hb : d326493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318995 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318995, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88667 q ha hb
    | true =>
      simp only [d318995, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88668 q ha hb
  have h3 (q : Pattern) (ha : d319096 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319096, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319096, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319100 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319100, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319100, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319121 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319121, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319121, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319122 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319122, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319122, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319123 q = 1) (hb : d326493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319123, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319123, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88939 (p : Pattern) (ha : d319191 p = 1) (hb : d326504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319180 q = 1) (hb : d326499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319180, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88702 q ha hb
    | true =>
      simp only [d319180, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88705 q ha hb
  have h3 (q : Pattern) (ha : d319181 q = 1) (hb : d326500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319181, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319181, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319188 q = 1) (hb : d326501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319188, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319188, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319189 q = 1) (hb : d326502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319189, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319189, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319190 q = 1) (hb : d326503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319190, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319190, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319191 q = 1) (hb : d326504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319191, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319191, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88940 (p : Pattern) (ha : d319204 p = 1) (hb : d326510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319003 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319104 q = 1) (hb : d325574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319104, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88936 q ha hb
    | true =>
      simp only [d319104, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88937 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319118 q = 1) (hb : d325575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319118, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319118, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319119 q = 1) (hb : d326491 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319119, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319119, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319120 q = 1) (hb : d326492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319120, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319120, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319124 q = 1) (hb : d326494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319124, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319124, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88938 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319126 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319127 q = 1) (hb : d326495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319127, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319127, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319128 q = 1) (hb : d326496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319128, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319128, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319129 q = 1) (hb : d326497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319129, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319129, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319130 q = 1) (hb : d326498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319130, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319130, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319192 q = 1) (hb : d326505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319192, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319192, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88939 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319200 q = 1) (hb : d326506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319200, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319200, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319201 q = 1) (hb : d326507 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319201, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319201, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319202 q = 1) (hb : d326508 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319202, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319202, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319203 q = 1) (hb : d326509 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319203, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319203, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319204 q = 1) (hb : d326510 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319204, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319204, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88941 (p : Pattern) (ha : d319210 p = 1) (hb : d326516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319205 q = 1) (hb : d326511 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319205, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319205, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88940 q ha hb
  have h2 (q : Pattern) (ha : d319206 q = 1) (hb : d326512 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319206, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319206, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319207 q = 1) (hb : d326513 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319207, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319207, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319208 q = 1) (hb : d326514 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319208, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319208, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319209 q = 1) (hb : d326515 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319209, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319209, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319210 q = 1) (hb : d326516 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319210, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319210, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88942 (p : Pattern) (ha : d319354 p = 1) (hb : d325812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d319247 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319247, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88715 q ha hb
    | true =>
      simp only [d319247, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88716 q ha hb
  have h5 (q : Pattern) (ha : d319344 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319344, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319344, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d319351 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319351, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319351, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d319352 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319352, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319352, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319353 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319353, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319353, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319354 q = 1) (hb : d325812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319354, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319354, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88943 (p : Pattern) (ha : d319375 p = 1) (hb : d325822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319247 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319247, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88715 q ha hb
    | true =>
      simp only [d319247, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88716 q ha hb
  have h4 (q : Pattern) (ha : d319344 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319344, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319344, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d319351 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319351, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319351, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319352 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319352, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319352, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319353 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319353, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319353, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319360 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319365 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d319257 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319257, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88718 q ha hb
    | true =>
      simp only [d319257, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88719 q ha hb
  have h13 (q : Pattern) (ha : d319368 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319368, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319368, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319372 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319372, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319372, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319373 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319373, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d319373, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319374 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319374, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d319374, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319375 q = 1) (hb : d325822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319375, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319375, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88944 (p : Pattern) (ha : d319395 p = 1) (hb : d326520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319257 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319257, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88718 q ha hb
    | true =>
      simp only [d319257, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88719 q ha hb
  have h3 (q : Pattern) (ha : d319368 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319368, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319368, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319372 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319372, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319372, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319393 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319393, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319393, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319394 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319394, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319394, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319395 q = 1) (hb : d326520 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319395, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319395, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88945 (p : Pattern) (ha : d319480 p = 1) (hb : d326531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319469 q = 1) (hb : d326526 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319469, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88757 q ha hb
    | true =>
      simp only [d319469, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88760 q ha hb
  have h3 (q : Pattern) (ha : d319470 q = 1) (hb : d326527 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319470, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319470, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319477 q = 1) (hb : d326528 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319477, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319477, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319478 q = 1) (hb : d326529 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319478, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319478, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319479 q = 1) (hb : d326530 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319479, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319479, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319480 q = 1) (hb : d326531 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319480, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319480, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88946 (p : Pattern) (ha : d319493 p = 1) (hb : d326537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319376 q = 1) (hb : d325823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319376, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88942 q ha hb
    | true =>
      simp only [d319376, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88943 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319390 q = 1) (hb : d325824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319390, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319390, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319391 q = 1) (hb : d326518 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319391, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319391, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319392 q = 1) (hb : d326519 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319392, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319392, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319396 q = 1) (hb : d326521 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319396, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319396, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88944 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319398 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319399 q = 1) (hb : d326522 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319399, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319399, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319400 q = 1) (hb : d326523 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319400, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319400, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319401 q = 1) (hb : d326524 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319401, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319401, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319402 q = 1) (hb : d326525 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319402, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319402, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319481 q = 1) (hb : d326532 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319481, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319481, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88945 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319489 q = 1) (hb : d326533 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319489, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319489, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319490 q = 1) (hb : d326534 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319490, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319490, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319491 q = 1) (hb : d326535 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319491, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319491, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319492 q = 1) (hb : d326536 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319492, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319492, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319493 q = 1) (hb : d326537 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319493, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319493, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88947 (p : Pattern) (ha : d319499 p = 1) (hb : d326543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319494 q = 1) (hb : d326538 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319494, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319494, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88946 q ha hb
  have h2 (q : Pattern) (ha : d319495 q = 1) (hb : d326539 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319495, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319495, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319496 q = 1) (hb : d326540 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319496, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319496, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319497 q = 1) (hb : d326541 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319497, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319497, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319498 q = 1) (hb : d326542 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319498, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319498, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319499 q = 1) (hb : d326543 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319499, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319499, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88948 (p : Pattern) (ha : d319705 p = 1) (hb : d326140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d319593 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
    | true =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
  have h5 (q : Pattern) (ha : d319686 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319686, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d319702 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319702, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d319703 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319703, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319704 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319704, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319705 q = 1) (hb : d326140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319705, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319705, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88949 (p : Pattern) (ha : d319726 p = 1) (hb : d326150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319593 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88775 q ha hb
    | true =>
      simp only [d319593, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88776 q ha hb
  have h4 (q : Pattern) (ha : d319686 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319686, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d319702 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319702, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319703 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319703, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319704 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319704, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319711 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319716 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d319603 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319603, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88778 q ha hb
    | true =>
      simp only [d319603, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88779 q ha hb
  have h13 (q : Pattern) (ha : d319719 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319719, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319723 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319723, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319724 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319724, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d319724, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319725 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319725, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d319725, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319726 q = 1) (hb : d326150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319726, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319726, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88950 (p : Pattern) (ha : d319746 p = 1) (hb : d326548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319603 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319603, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88778 q ha hb
    | true =>
      simp only [d319603, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88779 q ha hb
  have h3 (q : Pattern) (ha : d319719 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319719, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319723 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319723, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319744 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319744, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319744, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319745 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319745, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319745, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319746 q = 1) (hb : d326548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319746, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319746, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88951 (p : Pattern) (ha : d319867 p = 1) (hb : d326559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319847 q = 1) (hb : d326554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319847, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88817 q ha hb
    | true =>
      simp only [d319847, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88822 q ha hb
  have h3 (q : Pattern) (ha : d319848 q = 1) (hb : d326555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319848, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319848, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319863 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319864 q = 1) (hb : d326556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319864, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319864, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319865 q = 1) (hb : d326557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319865, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319865, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319866 q = 1) (hb : d326558 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319866, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319866, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319867 q = 1) (hb : d326559 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319867, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319867, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88952 (p : Pattern) (ha : d319880 p = 1) (hb : d326565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319727 q = 1) (hb : d326151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319727, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88948 q ha hb
    | true =>
      simp only [d319727, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88949 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319740 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319741 q = 1) (hb : d326152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319741, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319741, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319742 q = 1) (hb : d326546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319742, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319742, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319743 q = 1) (hb : d326547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319743, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319743, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319747 q = 1) (hb : d326549 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319747, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319747, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88950 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319749 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319750 q = 1) (hb : d326550 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319750, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319750, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319751 q = 1) (hb : d326551 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319751, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319751, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319752 q = 1) (hb : d326552 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319752, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319752, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319753 q = 1) (hb : d326553 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319753, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319753, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319868 q = 1) (hb : d326560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319868, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319868, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88951 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319875 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319876 q = 1) (hb : d326561 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319876, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319876, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319877 q = 1) (hb : d326562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319877, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319877, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319878 q = 1) (hb : d326563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319878, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319878, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319879 q = 1) (hb : d326564 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319879, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319879, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319880 q = 1) (hb : d326565 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319880, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319880, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88953 (p : Pattern) (ha : d319886 p = 1) (hb : d326571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319881 q = 1) (hb : d326566 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319881, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319881, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88952 q ha hb
  have h2 (q : Pattern) (ha : d319882 q = 1) (hb : d326567 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319882, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319882, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319883 q = 1) (hb : d326568 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319883, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319883, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319884 q = 1) (hb : d326569 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319884, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319884, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319885 q = 1) (hb : d326570 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319885, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319885, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319886 q = 1) (hb : d326571 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319886, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319886, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88954 (p : Pattern) (ha : d320029 p = 1) (hb : d324661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319979 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d319953 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
    | true =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
  have h5 (q : Pattern) (ha : d320003 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320003, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d320003, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d320025 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d320026 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320026, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320026, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d320027 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320027, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d320027, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320028 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320028, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320028, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320029 q = 1) (hb : d324661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320029, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320029, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88955 (p : Pattern) (ha : d320050 p = 1) (hb : d324671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319979 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319953 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88834 q ha hb
    | true =>
      simp only [d319953, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88835 q ha hb
  have h4 (q : Pattern) (ha : d320003 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320003, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d320003, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d320025 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d320026 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320026, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320026, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d320027 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320027, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320027, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320028 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320028, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320028, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d320035 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d320040 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d320042 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d319963 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319963, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88837 q ha hb
    | true =>
      simp only [d319963, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88838 q ha hb
  have h13 (q : Pattern) (ha : d320043 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320043, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d320043, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320046 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320047 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320047, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320047, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d320048 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320048, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d320048, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320049 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320049, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d320049, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d320050 q = 1) (hb : d324671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320050, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320050, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88956 (p : Pattern) (ha : d320070 p = 1) (hb : d325181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319963 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319963, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88837 q ha hb
    | true =>
      simp only [d319963, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88838 q ha hb
  have h3 (q : Pattern) (ha : d320043 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320043, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320043, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320047 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320047, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320047, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320068 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320068, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320068, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320069 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320069, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320069, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320070 q = 1) (hb : d325181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320070, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320070, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88957 (p : Pattern) (ha : d320161 p = 1) (hb : d325192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d320135 q = 1) (hb : d325187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320135, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88872 q ha hb
    | true =>
      simp only [d320135, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88878 q ha hb
  have h3 (q : Pattern) (ha : d320136 q = 1) (hb : d325188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320136, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320136, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320158 q = 1) (hb : d325189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320158, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320158, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320159 q = 1) (hb : d325190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320159, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320159, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320160 q = 1) (hb : d325191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320160, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320160, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320161 q = 1) (hb : d325192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320161, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320161, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88958 (p : Pattern) (ha : d320174 p = 1) (hb : d325198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320051 q = 1) (hb : d324672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320051, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88954 q ha hb
    | true =>
      simp only [d320051, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88955 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320064 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320065 q = 1) (hb : d324673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320065, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320065, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320066 q = 1) (hb : d325179 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320066, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320066, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320067 q = 1) (hb : d325180 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320067, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320067, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320071 q = 1) (hb : d325182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320071, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320071, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88956 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d320073 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d320074 q = 1) (hb : d325183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320074, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320074, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d320075 q = 1) (hb : d325184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320075, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320075, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d320076 q = 1) (hb : d325185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320076, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320076, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d320077 q = 1) (hb : d325186 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320077, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320077, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320162 q = 1) (hb : d325193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320162, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320162, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88957 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320170 q = 1) (hb : d325194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320170, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320170, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d320171 q = 1) (hb : d325195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320171, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320171, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d320172 q = 1) (hb : d325196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320172, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320172, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d320173 q = 1) (hb : d325197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320173, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320173, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d320174 q = 1) (hb : d325198 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d320174, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320174, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88959 (p : Pattern) (ha : d320180 p = 1) (hb : d325204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320175 q = 1) (hb : d325199 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d320175, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320175, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88958 q ha hb
  have h2 (q : Pattern) (ha : d320176 q = 1) (hb : d325200 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d320176, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320176, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320177 q = 1) (hb : d325201 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d320177, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320177, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320178 q = 1) (hb : d325202 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d320178, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320178, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320179 q = 1) (hb : d325203 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d320179, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320179, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320180 q = 1) (hb : d325204 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d320180, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320180, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88960 (p : Pattern) (ha : d269783 p = 1) (hb : d324333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44880 q = 1) (hb : d263912 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d263913 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d263913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46864, d263913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46865 q = 1) (hb : d263914 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d263914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46865, d263914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269782 q = 1) (hb : d324332 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d269782, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269782, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46866 q = 1) (hb : d263915 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, d263915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46866, d263915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d269783 q = 1) (hb : d324333 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d269783, d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269783, d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro88961 (p : Pattern) (ha : d320403 p = 1) (hb : d326581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320398 q = 1) (hb : d326576 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d320398, d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88960 q ha hb
    | true =>
      simp only [d320398, d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86234 q hb ha
  have h2 (q : Pattern) (ha : d320399 q = 1) (hb : d326577 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d320399, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320399, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320400 q = 1) (hb : d326578 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d320400, d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320400, d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46871 q = 1) (hb : d320189 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86234 q ha hb
    | true =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46872 q = 1) (hb : d320190 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46873 q = 1) (hb : d320191 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d320401 q = 1) (hb : d326579 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d320401, d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320401, d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d320402 q = 1) (hb : d326580 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d320402, d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320402, d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320403 q = 1) (hb : d326581 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d320403, d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320403, d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro88962 (p : Pattern) (ha : d320409 p = 1) (hb : d326587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d320351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d320352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d320353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d320354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d320360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d320366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86238 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d320207 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86238 q ha hb
    | true =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d320367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320404 q = 1) (hb : d326582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320404, d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88961 q ha hb
    | true =>
      simp only [d320404, d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320405 q = 1) (hb : d326583 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320405, d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320405, d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d320406 q = 1) (hb : d326584 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320406, d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d320406, d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320407 q = 1) (hb : d326585 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320407, d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320407, d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d320408 q = 1) (hb : d326586 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320408, d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d320408, d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d320409 q = 1) (hb : d326587 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320409, d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d320409, d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro88963 (p : Pattern) (ha : d320415 p = 1) (hb : d326593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320410 q = 1) (hb : d326588 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320410, d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q hb ha
    | true =>
      simp only [d320410, d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88962 q ha hb
  have h2 (q : Pattern) (ha : d320411 q = 1) (hb : d326589 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320411, d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320411, d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320412 q = 1) (hb : d326590 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320412, d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320412, d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320413 q = 1) (hb : d326591 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320413, d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320413, d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320414 q = 1) (hb : d326592 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320414, d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320414, d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320415 q = 1) (hb : d326593 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320415, d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320415, d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88964 (p : Pattern) (ha : d320421 p = 1) (hb : d326599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320416 q = 1) (hb : d326594 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320416, d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88963 q ha hb
    | true =>
      simp only [d320416, d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320417 q = 1) (hb : d326595 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320417, d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320417, d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320418 q = 1) (hb : d326596 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320418, d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320418, d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320419 q = 1) (hb : d326597 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320419, d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320419, d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320420 q = 1) (hb : d326598 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320420, d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320420, d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320421 q = 1) (hb : d326599 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320421, d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320421, d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88965 (p : Pattern) (ha : d320442 p = 1) (hb : d326605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d320422 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320422, d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86278 q hb ha
    | true =>
      simp only [d320422, d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88964 q ha hb
  have h3 (q : Pattern) (ha : d320423 q = 1) (hb : d326601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320423, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320423, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320439 q = 1) (hb : d326602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320439, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320439, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320440 q = 1) (hb : d326603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320440, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320440, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320441 q = 1) (hb : d326604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320441, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320441, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320442 q = 1) (hb : d326605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320442, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320442, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88966 (p : Pattern) (ha : d320459 p = 1) (hb : d326611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d320252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d320324 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d320324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86366 q ha hb
    | true =>
      simp only [d46932, d320324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86367 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d320338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d320338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d320338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320339 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320339, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d320339, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320340 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320340, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320340, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320344 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320344, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320344, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86368 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d320346 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d320347 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320347, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320347, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d320348 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320348, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320348, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d320349 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320349, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320349, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d320350 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320350, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320350, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320443 q = 1) (hb : d326606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320443, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320443, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88965 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320454 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320455 q = 1) (hb : d326607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320455, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320455, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d320456 q = 1) (hb : d326608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320456, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320456, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d320457 q = 1) (hb : d326609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320457, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320457, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d320458 q = 1) (hb : d326610 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320458, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320458, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d320459 q = 1) (hb : d326611 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d320459, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320459, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88967 (p : Pattern) (ha : d320465 p = 1) (hb : d326617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320460 q = 1) (hb : d326612 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d320460, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320460, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88966 q ha hb
  have h2 (q : Pattern) (ha : d320461 q = 1) (hb : d326613 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d320461, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320461, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320462 q = 1) (hb : d326614 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d320462, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320462, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320463 q = 1) (hb : d326615 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d320463, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320463, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320464 q = 1) (hb : d326616 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d320464, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320464, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320465 q = 1) (hb : d326617 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d320465, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320465, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88968 (p : Pattern) (ha : d320471 p = 1) (hb : d326623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d326517 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88935 q ha hb
    | true =>
      simp only [d319211, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88941 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d326544 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88947 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d326545 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d326572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88953 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d326573 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d326574 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d325205 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88959 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d325206 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d325207 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d326575 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320466 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320466, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320466, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88967 q ha hb
  have h12 (q : Pattern) (ha : d320467 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320467, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320467, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320468 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320468, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320468, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320469 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320469, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320469, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320470 q = 1) (hb : d326622 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320471 q = 1) (hb : d326623 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320471, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro88969 (p : Pattern) (ha : d320477 p = 1) (hb : d326629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d326624 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88968 q ha hb
    | true =>
      simp only [d320472, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d326625 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d326626 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d326627 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d326628 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d326629 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88970 (p : Pattern) (ha : d320483 p = 1) (hb : d326635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d326630 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88969 q ha hb
    | true =>
      simp only [d320478, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d326631 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d326632 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d326633 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d326634 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d326635 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88971 (p : Pattern) (ha : d320489 p = 1) (hb : d326641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d326636 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88970 q ha hb
    | true =>
      simp only [d320484, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d326637 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d326638 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d326639 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d326640 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d326641 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88972 (p : Pattern) (ha : d320495 p = 1) (hb : d326647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d326642 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88971 q ha hb
    | true =>
      simp only [d320490, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d326643 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d326644 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d326645 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d326646 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d326647 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88973 (p : Pattern) (ha : d320501 p = 1) (hb : d326653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d326648 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88972 q ha hb
    | true =>
      simp only [d320496, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d326649 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d326650 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d326651 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d326652 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d326653 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88974 (p : Pattern) (ha : d320507 p = 1) (hb : d326659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d326654 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88973 q ha hb
    | true =>
      simp only [d320502, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d326655 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d326656 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d326657 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d326658 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d326659 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88975 (p : Pattern) (ha : d320513 p = 1) (hb : d326665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d326660 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88974 q ha hb
    | true =>
      simp only [d320508, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d326661 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d326662 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d326663 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d326664 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d326665 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro88976 (p : Pattern) (ha : d321643 p = 1) (hb : d324661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46548 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46557 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321639 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321639, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d321639, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d46658 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d321640 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321640, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321640, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d321641 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321641, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d321641, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321642 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321642, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321642, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321643 q = 1) (hb : d324661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321643, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321643, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88977 (p : Pattern) (ha : d321648 p = 1) (hb : d324671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d321639 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321639, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d321639, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d46658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d321640 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321640, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321640, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d321641 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321641, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321641, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321642 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321642, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321642, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d46668 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d46673 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d46675 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d321644 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321644, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d321644, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321645 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321645, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321645, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d321646 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321646, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d321646, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d321647 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321647, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d321647, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d321648 q = 1) (hb : d324671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321648, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321648, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88978 (p : Pattern) (ha : d321655 p = 1) (hb : d325181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46675 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321644 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321644, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321644, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321645 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321645, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321645, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d321653 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321653, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321653, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321654 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321654, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321654, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321655 q = 1) (hb : d325181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321655, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321655, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88979 (p : Pattern) (ha : d321665 p = 1) (hb : d325192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325187 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321661 q = 1) (hb : d325188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321661, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321661, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321662 q = 1) (hb : d325189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321662, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321662, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d321663 q = 1) (hb : d325190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321663, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321663, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321664 q = 1) (hb : d325191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321664, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321664, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321665 q = 1) (hb : d325192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321665, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321665, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88980 (p : Pattern) (ha : d321671 p = 1) (hb : d325198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46540 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321649 q = 1) (hb : d324672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321649, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88976 q ha hb
    | true =>
      simp only [d321649, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88977 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46700 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321650 q = 1) (hb : d324673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321650, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321650, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321651 q = 1) (hb : d325179 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321651, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321651, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321652 q = 1) (hb : d325180 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321652, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321652, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321656 q = 1) (hb : d325182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321656, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321656, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88978 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d46709 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321657 q = 1) (hb : d325183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321657, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321657, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d321658 q = 1) (hb : d325184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321658, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321658, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321659 q = 1) (hb : d325185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321659, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321659, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321660 q = 1) (hb : d325186 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321660, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321660, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321666 q = 1) (hb : d325193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321666, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321666, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88979 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46848 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321667 q = 1) (hb : d325194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321667, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321667, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d321668 q = 1) (hb : d325195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321668, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321668, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321669 q = 1) (hb : d325196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321669, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321669, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321670 q = 1) (hb : d325197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321670, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321670, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321671 q = 1) (hb : d325198 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321671, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321671, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88981 (p : Pattern) (ha : d321677 p = 1) (hb : d325204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321672 q = 1) (hb : d325199 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321672, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321672, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88980 q ha hb
  have h2 (q : Pattern) (ha : d321673 q = 1) (hb : d325200 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321673, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321673, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321674 q = 1) (hb : d325201 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321674, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321674, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321675 q = 1) (hb : d325202 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321675, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321675, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321676 q = 1) (hb : d325203 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321676, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321676, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321677 q = 1) (hb : d325204 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321677, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321677, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88982 (p : Pattern) (ha : d321708 p = 1) (hb : d326605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d47132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321704 q = 1) (hb : d326601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321704, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321704, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d47207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321705 q = 1) (hb : d326602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321705, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321705, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d321706 q = 1) (hb : d326603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321706, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321706, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321707 q = 1) (hb : d326604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321707, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321707, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321708 q = 1) (hb : d326605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321708, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321708, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88983 (p : Pattern) (ha : d321714 p = 1) (hb : d326611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d321692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86390 q ha hb
    | true =>
      simp only [d46932, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86391 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d47072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d321693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321694 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321694, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d321694, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321695 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321695, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321695, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321699 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321699, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321699, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86392 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d47081 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321700 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321700, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321700, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d321701 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321701, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321701, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321702 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321702, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321702, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321703 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321703, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321703, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321709 q = 1) (hb : d326606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321709, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321709, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88982 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d47223 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321710 q = 1) (hb : d326607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321710, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321710, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d321711 q = 1) (hb : d326608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321711, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321711, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321712 q = 1) (hb : d326609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321712, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321712, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321713 q = 1) (hb : d326610 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321713, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321713, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321714 q = 1) (hb : d326611 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321714, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321714, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88984 (p : Pattern) (ha : d321720 p = 1) (hb : d326617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321715 q = 1) (hb : d326612 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321715, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321715, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88983 q ha hb
  have h2 (q : Pattern) (ha : d321716 q = 1) (hb : d326613 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321716, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321716, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321717 q = 1) (hb : d326614 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321717, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321717, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321718 q = 1) (hb : d326615 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321718, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321718, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321719 q = 1) (hb : d326616 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321719, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321719, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321720 q = 1) (hb : d326617 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321720, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321720, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88985 (p : Pattern) (ha : d322048 p = 1) (hb : d325396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45031 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322044 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322044, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322044, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45067 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d322045 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322045, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322045, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d322046 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322046, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322046, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322047 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322047, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322047, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322048 q = 1) (hb : d325396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322048, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322048, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88986 (p : Pattern) (ha : d322053 p = 1) (hb : d325403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322044 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322044, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322044, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d322045 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322045, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322045, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d322046 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322046, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322046, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322047 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322047, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322047, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45076 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45080 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45082 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d322049 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322049, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d322049, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45088 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322050 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322050, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322050, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322051 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322051, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d322051, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d322052 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322052, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d322052, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d322053 q = 1) (hb : d325403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322053, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322053, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88987 (p : Pattern) (ha : d322060 p = 1) (hb : d326468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322049 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322049, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322049, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322050 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322050, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322050, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322058 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322058, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322058, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322059 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322059, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322059, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322060 q = 1) (hb : d326468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322060, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322060, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88988 (p : Pattern) (ha : d322070 p = 1) (hb : d326478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325375 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322066 q = 1) (hb : d326474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322066, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322066, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322067 q = 1) (hb : d326475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322067, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322067, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322068 q = 1) (hb : d326476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322068, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322068, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322069 q = 1) (hb : d326477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322069, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322069, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322070 q = 1) (hb : d326478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322070, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322070, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88989 (p : Pattern) (ha : d322076 p = 1) (hb : d326484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322054 q = 1) (hb : d325404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322054, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88985 q ha hb
    | true =>
      simp only [d322054, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88986 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322055 q = 1) (hb : d325405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322055, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322055, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322056 q = 1) (hb : d326466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322056, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322056, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322057 q = 1) (hb : d326467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322057, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322057, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322061 q = 1) (hb : d326469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322061, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322061, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88987 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d322062 q = 1) (hb : d326470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322062, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322062, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d322063 q = 1) (hb : d326471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322063, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322063, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d322064 q = 1) (hb : d326472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322064, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322064, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d322065 q = 1) (hb : d326473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322065, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322065, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322071 q = 1) (hb : d326479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322071, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322071, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88988 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322072 q = 1) (hb : d326480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322072, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322072, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322073 q = 1) (hb : d326481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322073, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322073, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d322074 q = 1) (hb : d326482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322074, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322074, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d322075 q = 1) (hb : d326483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322075, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322075, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d322076 q = 1) (hb : d326484 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322076, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322076, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88990 (p : Pattern) (ha : d322082 p = 1) (hb : d326490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86400 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322077 q = 1) (hb : d326485 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322077, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322077, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88989 q ha hb
  have h8 (q : Pattern) (ha : d322078 q = 1) (hb : d326486 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322078, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322078, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322079 q = 1) (hb : d326487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322079, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322079, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322080 q = 1) (hb : d326488 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322080, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322080, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d322081 q = 1) (hb : d326489 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322081, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322081, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d322082 q = 1) (hb : d326490 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322082, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d322082, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro88991 (p : Pattern) (ha : d322087 p = 1) (hb : d325563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45216 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45276 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322083 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322083, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322083, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d322084 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322084, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322084, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d322085 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322085, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322085, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322086 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322086, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322086, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322087 q = 1) (hb : d325563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322087, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322087, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88992 (p : Pattern) (ha : d322092 p = 1) (hb : d325573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45216 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322083 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322083, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322083, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d322084 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322084, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322084, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d322085 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322085, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322085, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322086 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322086, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322086, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45345 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d322088 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322088, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d322088, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322089 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322089, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322089, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322090 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322090, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d322090, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d322091 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322091, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d322091, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d322092 q = 1) (hb : d325573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322092, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322092, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88993 (p : Pattern) (ha : d322099 p = 1) (hb : d326493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45345 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322088 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322088, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322088, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45352 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322089 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322089, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322089, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322097 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322097, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322097, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322098 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322098, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322098, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322099 q = 1) (hb : d326493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322099, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322099, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88994 (p : Pattern) (ha : d322109 p = 1) (hb : d326504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326499 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322105 q = 1) (hb : d326500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322105, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322105, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45468 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322106 q = 1) (hb : d326501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322106, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322106, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322107 q = 1) (hb : d326502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322107, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322107, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322108 q = 1) (hb : d326503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322108, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322108, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322109 q = 1) (hb : d326504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322109, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322109, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro88995 (p : Pattern) (ha : d322115 p = 1) (hb : d326510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45208 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322093 q = 1) (hb : d325574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322093, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88991 q ha hb
    | true =>
      simp only [d322093, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88992 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322094 q = 1) (hb : d325575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322094, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322094, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322095 q = 1) (hb : d326491 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322095, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322095, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322096 q = 1) (hb : d326492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322096, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322096, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322100 q = 1) (hb : d326494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322100, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322100, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88993 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d45379 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d322101 q = 1) (hb : d326495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322101, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322101, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d322102 q = 1) (hb : d326496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322102, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322102, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d322103 q = 1) (hb : d326497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322103, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322103, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d322104 q = 1) (hb : d326498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322104, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322104, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322110 q = 1) (hb : d326505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322110, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322110, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88994 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45484 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322111 q = 1) (hb : d326506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322111, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322111, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322112 q = 1) (hb : d326507 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322112, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322112, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d322113 q = 1) (hb : d326508 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322113, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322113, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d322114 q = 1) (hb : d326509 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322114, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322114, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d322115 q = 1) (hb : d326510 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322115, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322115, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro88996 (p : Pattern) (ha : d322121 p = 1) (hb : d326516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322116 q = 1) (hb : d326511 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322116, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322116, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88995 q ha hb
  have h2 (q : Pattern) (ha : d322117 q = 1) (hb : d326512 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322117, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322117, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322118 q = 1) (hb : d326513 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322118, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322118, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322119 q = 1) (hb : d326514 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322119, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322119, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322120 q = 1) (hb : d326515 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322120, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322120, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322121 q = 1) (hb : d326516 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322121, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322121, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro88997 (p : Pattern) (ha : d322127 p = 1) (hb : d325812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45558 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45628 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322123 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322123, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322123, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45703 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d322124 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322124, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322124, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d322125 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322125, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322125, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322126 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322126, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322126, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322127 q = 1) (hb : d325812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322127, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322127, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro88998 (p : Pattern) (ha : d322132 p = 1) (hb : d325822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322123 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322123, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322123, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45703 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d322124 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322124, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322124, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d322125 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322125, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322125, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322126 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322126, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322126, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45713 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45718 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45720 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d322128 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322128, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d322128, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45727 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322129 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322129, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322129, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322130 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322130, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d322130, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d322131 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322131, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d322131, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d322132 q = 1) (hb : d325822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322132, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322132, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro88999 (p : Pattern) (ha : d322139 p = 1) (hb : d326520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45720 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322128 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322128, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322128, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322129 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322129, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322129, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322137 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322137, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322137, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322138 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322138, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322138, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322139 q = 1) (hb : d326520 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322139, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322139, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
