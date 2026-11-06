import NetHack.Soko22Hazard87.AndIntroBlocks0136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro34250 (p : Pattern) (ha : d14761 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1103 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1103, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14757 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14759 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14759, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14760 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14760, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14760, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14761 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34251 (p : Pattern) (ha : d14766 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1113 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1113, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14762 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14762, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14762, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14763 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14764 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14764, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14765 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14765, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14766 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34252 (p : Pattern) (ha : d14773 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5020 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5021 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5021, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5022 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5022, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14771 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14771, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14772 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14772, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14773 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34253 (p : Pattern) (ha : d14778 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1124 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1124, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1127 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1127, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14771 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14771, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14772 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14772, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14778 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34254 (p : Pattern) (ha : d14784 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34250 q ha hb
    | true =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14774 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34252 q ha hb
  have h5 (q : Pattern) (ha : d14775 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14776 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14777 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14779 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34253 q ha hb
  have h9 (q : Pattern) (ha : d14780 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14781 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14782 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14783 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14784 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34255 (p : Pattern) (ha : d14788 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14779 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34253 q ha hb
  have h2 (q : Pattern) (ha : d14780 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14781 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14782 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14787 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14788 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34256 (p : Pattern) (ha : d14794 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34254 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14794 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34257 (p : Pattern) (ha : d14798 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14798 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34258 (p : Pattern) (ha : d14804 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34256 q ha hb
    | true =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34257 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14804 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34259 (p : Pattern) (ha : d14807 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34254 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14807 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34260 (p : Pattern) (ha : d14808 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14808 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34261 (p : Pattern) (ha : d14814 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34256 q ha hb
    | true =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34257 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14809 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34259 q ha hb
    | true =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34260 q ha hb
  have h7 (q : Pattern) (ha : d14810 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14811 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14812 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14813 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14814 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34262 (p : Pattern) (ha : d14855 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34250 q ha hb
    | true =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14774 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34252 q ha hb
  have h5 (q : Pattern) (ha : d14775 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14776 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14777 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14853 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14854 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14855 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34263 (p : Pattern) (ha : d14865 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34262 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14865 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34264 (p : Pattern) (ha : d14965 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14955 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34263 q ha hb
    | true =>
      simp only [d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34257 q ha hb
  have h2 (q : Pattern) (ha : d14956 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14957 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14958 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14959 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14960 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34257 q ha hb
    | true =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14961 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14962 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14963 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14964 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14965 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34265 (p : Pattern) (ha : d14971 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14960 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34257 q ha hb
    | true =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14961 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14962 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14963 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14964 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14966 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34260 q ha hb
    | true =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14967 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14968 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14969 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14970 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14971 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34266 (p : Pattern) (ha : d14980 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14966 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34260 q ha hb
    | true =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14967 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14968 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14969 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14970 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34267 (p : Pattern) (ha : d15015 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1388 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1388, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15014 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15014, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15014, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15006 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15007 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15007, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15008 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15008, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15015 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34268 (p : Pattern) (ha : d15042 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1394 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1394, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1400 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1400, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15022 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15022, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15023, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15042 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34269 (p : Pattern) (ha : d15048 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15043 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34268 q ha hb
  have h2 (q : Pattern) (ha : d15044 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15045 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15046 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15047 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15048 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34270 (p : Pattern) (ha : d15128 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15049 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34269 q ha hb
    | true =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15050 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15125 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15126 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15127 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15128 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34271 (p : Pattern) (ha : d15134 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15129 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34270 q ha hb
    | true =>
      simp only [d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15130 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15131 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15132 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15133 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15134 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34272 (p : Pattern) (ha : d14819 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34254 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14819 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34273 (p : Pattern) (ha : d14821 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14821 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34274 (p : Pattern) (ha : d14828 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34254 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14828 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34275 (p : Pattern) (ha : d14831 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14831 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34276 (p : Pattern) (ha : d14839 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1213 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1213, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14835 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14835, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14835, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14836 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14837 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14837, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14838 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14838, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14838, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14839 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34277 (p : Pattern) (ha : d14844 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13023 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13023, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14843 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14843, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14843, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14763 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14764 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14764, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14765 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14765, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14844 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34278 (p : Pattern) (ha : d14850 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14840 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34276 q ha hb
    | true =>
      simp only [d14840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34250 q ha hb
  have h2 (q : Pattern) (ha : d14841 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14842 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14845 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34250 q ha hb
    | true =>
      simp only [d14845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34277 q ha hb
  have h5 (q : Pattern) (ha : d14846 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14847 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14848 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14767 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34250 q ha hb
    | true =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
  have h9 (q : Pattern) (ha : d14768 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14769 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14774 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34252 q ha hb
  have h12 (q : Pattern) (ha : d14775 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14776 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14777 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14849 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14850 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34279 (p : Pattern) (ha : d14861 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34278 q ha hb
    | true =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34262 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14861 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34280 (p : Pattern) (ha : d12961 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1124 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1124, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1127 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1127, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12961 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34281 (p : Pattern) (ha : d14916 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34250 q ha hb
    | true =>
      simp only [d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14774 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34252 q ha hb
  have h5 (q : Pattern) (ha : d14775 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14776 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14777 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14911 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34251 q ha hb
    | true =>
      simp only [d14911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34280 q ha hb
  have h9 (q : Pattern) (ha : d14912 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14913 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14914 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14915 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14916 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34282 (p : Pattern) (ha : d14922 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34281 q ha hb
    | true =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14922 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34283 (p : Pattern) (ha : d125575 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34272 q ha hb
    | true =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34273 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34274 q ha hb
    | true =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34275 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34279 q ha hb
    | true =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34263 q ha hb
  have h9 (q : Pattern) (ha : d125571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34282 q ha hb
    | true =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125573 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34284 (p : Pattern) (ha : d14929 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34254 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14929 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34285 (p : Pattern) (ha : d14930 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14930 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34286 (p : Pattern) (ha : d14935 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34254 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14935 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34287 (p : Pattern) (ha : d14936 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14936 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34288 (p : Pattern) (ha : d14940 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34278 q ha hb
    | true =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34262 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14940 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34289 (p : Pattern) (ha : d14941 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34262 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34255 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14941 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34290 (p : Pattern) (ha : d14947 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34281 q ha hb
    | true =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14947 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34291 (p : Pattern) (ha : d125580 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34272 q ha hb
    | true =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34273 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34274 q ha hb
    | true =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34275 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34279 q ha hb
    | true =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34263 q ha hb
  have h9 (q : Pattern) (ha : d125571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34282 q ha hb
    | true =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125573 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14931 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34284 q ha hb
    | true =>
      simp only [d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34285 q ha hb
  have h16 (q : Pattern) (ha : d14932 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14933 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14934 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14937 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34286 q ha hb
    | true =>
      simp only [d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34287 q ha hb
  have h20 (q : Pattern) (ha : d14938 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14939 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14942 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34288 q ha hb
    | true =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34289 q ha hb
  have h23 (q : Pattern) (ha : d125576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14948 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34290 q ha hb
    | true =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14949 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125578 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125579 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34292 (p : Pattern) (ha : d125587 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14942 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34288 q ha hb
    | true =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34289 q ha hb
  have h2 (q : Pattern) (ha : d125576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14948 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34290 q ha hb
    | true =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14949 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125585 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34293 (p : Pattern) (ha : d14992 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1379 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1379, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14986 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14986, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14986, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14989 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14990 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14990, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14991, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14991, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34294 (p : Pattern) (ha : d14999 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1383 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1383, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14993 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14993, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14993, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14996 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14997 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14997, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14998 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14998, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14998, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14999 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34295 (p : Pattern) (ha : d15009 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13162 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13163 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13163, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15003 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15003, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15003, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15006 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15007 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15007, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15008 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15008, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15009 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34296 (p : Pattern) (ha : d15024 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6352 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6353 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6353, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6354, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15022 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15022, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15023, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15024 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34297 (p : Pattern) (ha : d15030 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15000 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34293 q ha hb
    | true =>
      simp only [d15000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34294 q ha hb
  have h2 (q : Pattern) (ha : d15001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15002 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15010 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34294 q ha hb
    | true =>
      simp only [d15010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34295 q ha hb
  have h5 (q : Pattern) (ha : d15011 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15012 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15013 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34294 q ha hb
    | true =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
  have h9 (q : Pattern) (ha : d15017 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15018 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15025 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34296 q ha hb
  have h12 (q : Pattern) (ha : d15026 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15029 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15030 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34298 (p : Pattern) (ha : d15035 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34294 q ha hb
    | true =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34296 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15033 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15034 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15035 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34299 (p : Pattern) (ha : d15041 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15031 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34297 q ha hb
    | true =>
      simp only [d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15032 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15036 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34298 q ha hb
    | true =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15037 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15038 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15039 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15040 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15041 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34300 (p : Pattern) (ha : d15054 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15036 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34298 q ha hb
    | true =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15037 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34269 q ha hb
    | true =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15051 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15052 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15053 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15054 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34301 (p : Pattern) (ha : d13190 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1394 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1394, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1400 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1400, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13190 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34302 (p : Pattern) (ha : d15111 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34294 q ha hb
    | true =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34296 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15106 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34301 q ha hb
  have h9 (q : Pattern) (ha : d15107 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15108 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15109 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15110 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15111 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34303 (p : Pattern) (ha : d15117 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15112 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34302 q ha hb
    | true =>
      simp only [d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15113 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15114 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15115 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15116 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15117 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34304 (p : Pattern) (ha : d125597 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15055 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34299 q ha hb
    | true =>
      simp only [d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34300 q ha hb
  have h2 (q : Pattern) (ha : d125593 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15118 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34303 q ha hb
    | true =>
      simp only [d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15119 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125594 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125595 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125596 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34305 (p : Pattern) (ha : d125603 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14805 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34258 q ha hb
  have h2 (q : Pattern) (ha : d14806 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14815 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34258 q ha hb
    | true =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34261 q ha hb
  have h4 (q : Pattern) (ha : d14816 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14817 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34283 q ha hb
    | true =>
      simp only [d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34291 q ha hb
  have h7 (q : Pattern) (ha : d14972 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34264 q ha hb
    | true =>
      simp only [d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34265 q ha hb
  have h8 (q : Pattern) (ha : d125582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125583 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34292 q ha hb
  have h12 (q : Pattern) (ha : d14981 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34266 q ha hb
  have h13 (q : Pattern) (ha : d125589 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125590 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125591 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125592 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34304 q ha hb
  have h18 (q : Pattern) (ha : d15135 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34271 q ha hb
  have h19 (q : Pattern) (ha : d125599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125601 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125602 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34306 (p : Pattern) (ha : d125609 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34305 q ha hb
  have h2 (q : Pattern) (ha : d125605 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125606 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125607 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125608 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34307 (p : Pattern) (ha : d15154 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1557 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1558 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1558, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15150 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15150, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15150, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15151 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15152 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15152, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15153 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15153, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15153, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15154 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34308 (p : Pattern) (ha : d15159 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1573 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1573, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15155 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15155, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15155, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15156 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15157 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15157, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15158 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15158, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15159 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34309 (p : Pattern) (ha : d15166 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5137 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5137, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5138 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5138, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15163 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15164 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15164, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15165 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15165, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15166 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34310 (p : Pattern) (ha : d15171 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1584 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1585 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1585, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1588, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15163 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15164 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15164, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15165 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15165, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15171 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34311 (p : Pattern) (ha : d15177 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34307 q ha hb
    | true =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34309 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15172 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34310 q ha hb
  have h9 (q : Pattern) (ha : d15173 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15174 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15175 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15176 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15177 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34312 (p : Pattern) (ha : d15181 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15172 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34310 q ha hb
  have h2 (q : Pattern) (ha : d15173 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15174 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15175 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15180 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15181 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34313 (p : Pattern) (ha : d15187 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34311 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15187 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34314 (p : Pattern) (ha : d15191 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15191 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34315 (p : Pattern) (ha : d15197 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34313 q ha hb
    | true =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34314 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15197 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34316 (p : Pattern) (ha : d15200 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34311 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15200 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34317 (p : Pattern) (ha : d15201 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15201 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34318 (p : Pattern) (ha : d15207 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34313 q ha hb
    | true =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34314 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15202 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34316 q ha hb
    | true =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34317 q ha hb
  have h7 (q : Pattern) (ha : d15203 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15204 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15205 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15206 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15207 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34319 (p : Pattern) (ha : d15248 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34307 q ha hb
    | true =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34309 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15246 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15247 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15248 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34320 (p : Pattern) (ha : d15258 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34319 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15258 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34321 (p : Pattern) (ha : d15358 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15348 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34320 q ha hb
    | true =>
      simp only [d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34314 q ha hb
  have h2 (q : Pattern) (ha : d15349 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15350 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15351 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34314 q ha hb
    | true =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15356 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15357 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15358 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34322 (p : Pattern) (ha : d15364 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34314 q ha hb
    | true =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15356 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15357 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15359 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34317 q ha hb
    | true =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15360 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15361 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15362 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15363 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15364 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34323 (p : Pattern) (ha : d15373 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15359 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34317 q ha hb
    | true =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15360 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15361 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15362 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15363 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15373 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34324 (p : Pattern) (ha : d15408 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1865 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1865, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15407 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15407, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15407, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15399 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15400 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15400, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15401 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15401, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15408 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34325 (p : Pattern) (ha : d15435 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1870 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1871 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1871, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1877 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1877, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15414 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15415 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15416 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15416, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15435 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34326 (p : Pattern) (ha : d15441 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15436 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34325 q ha hb
  have h2 (q : Pattern) (ha : d15437 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15438 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15439 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15440 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15441 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34327 (p : Pattern) (ha : d15521 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15442 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34326 q ha hb
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15443 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15518 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15519 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15520 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15521 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34328 (p : Pattern) (ha : d15527 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15522 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34327 q ha hb
    | true =>
      simp only [d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15523 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15524 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15525 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15526 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15527 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34329 (p : Pattern) (ha : d15212 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34311 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34330 (p : Pattern) (ha : d15214 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15214 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34331 (p : Pattern) (ha : d15221 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34311 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34332 (p : Pattern) (ha : d15224 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15224 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34333 (p : Pattern) (ha : d15232 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1667 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1668 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1668, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15228 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15228, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15228, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15229 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15230 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15230, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15231 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15231, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15231, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15232 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34334 (p : Pattern) (ha : d15237 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13349 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15236 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15236, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15236, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15156 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15157 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15157, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15158 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15158, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15237 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34335 (p : Pattern) (ha : d15243 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15233 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34333 q ha hb
    | true =>
      simp only [d15233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34307 q ha hb
  have h2 (q : Pattern) (ha : d15234 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15235 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15238 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34307 q ha hb
    | true =>
      simp only [d15238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34334 q ha hb
  have h5 (q : Pattern) (ha : d15239 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15240 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15241 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34307 q ha hb
    | true =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
  have h9 (q : Pattern) (ha : d15161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15167 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34309 q ha hb
  have h12 (q : Pattern) (ha : d15168 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15170 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15242 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15243 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34336 (p : Pattern) (ha : d15254 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34335 q ha hb
    | true =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34319 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15254 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34337 (p : Pattern) (ha : d13287 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1584 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1585 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1585, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1588, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13287 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34338 (p : Pattern) (ha : d15309 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34307 q ha hb
    | true =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34309 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15304 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34308 q ha hb
    | true =>
      simp only [d15304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34337 q ha hb
  have h9 (q : Pattern) (ha : d15305 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15306 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15307 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15308 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15309 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34339 (p : Pattern) (ha : d15315 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34338 q ha hb
    | true =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15315 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34340 (p : Pattern) (ha : d125617 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34329 q ha hb
    | true =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34330 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34331 q ha hb
    | true =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34332 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34336 q ha hb
    | true =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34320 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34339 q ha hb
    | true =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125617 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34341 (p : Pattern) (ha : d15322 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34311 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15322 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34342 (p : Pattern) (ha : d15323 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15323 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34343 (p : Pattern) (ha : d15328 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34311 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15328 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34344 (p : Pattern) (ha : d15329 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15329 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34345 (p : Pattern) (ha : d15333 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34335 q ha hb
    | true =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34319 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15333 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34346 (p : Pattern) (ha : d15334 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34319 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34312 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15334 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34347 (p : Pattern) (ha : d15340 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34338 q ha hb
    | true =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15340 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34348 (p : Pattern) (ha : d125622 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34329 q ha hb
    | true =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34330 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34331 q ha hb
    | true =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34332 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34336 q ha hb
    | true =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34320 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34339 q ha hb
    | true =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15324 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34341 q ha hb
    | true =>
      simp only [d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34342 q ha hb
  have h16 (q : Pattern) (ha : d15325 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15326 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15327 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15330 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34343 q ha hb
    | true =>
      simp only [d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34344 q ha hb
  have h20 (q : Pattern) (ha : d15331 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15332 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15335 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34345 q ha hb
    | true =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34346 q ha hb
  have h23 (q : Pattern) (ha : d125618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15341 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34347 q ha hb
    | true =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125620 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125621 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125622 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34349 (p : Pattern) (ha : d125629 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15335 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34345 q ha hb
    | true =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34346 q ha hb
  have h2 (q : Pattern) (ha : d125618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15341 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34347 q ha hb
    | true =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125627 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125628 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34350 (p : Pattern) (ha : d15385 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1856 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1856, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15379 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15379, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15379, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15382 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15383 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15383, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15384 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15384, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15384, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15385 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34351 (p : Pattern) (ha : d15392 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1859 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1860 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1860, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15386 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15386, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15386, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15389 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15390 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15390, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15391 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15391, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15391, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15392 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34352 (p : Pattern) (ha : d15402 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13488 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13489 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13489, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15396 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15396, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15396, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15399 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15400 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15400, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15401 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15401, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15402 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34353 (p : Pattern) (ha : d15417 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6498 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6499 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6499, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6500 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6500, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15414 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15415 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15416 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15416, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15417 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34354 (p : Pattern) (ha : d15423 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15393 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34350 q ha hb
    | true =>
      simp only [d15393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34351 q ha hb
  have h2 (q : Pattern) (ha : d15394 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15395 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15403 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34351 q ha hb
    | true =>
      simp only [d15403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34352 q ha hb
  have h5 (q : Pattern) (ha : d15404 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15405 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15406 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15409 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34351 q ha hb
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
  have h9 (q : Pattern) (ha : d15410 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15411 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34353 q ha hb
  have h12 (q : Pattern) (ha : d15419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15420 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15421 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15422 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15423 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34355 (p : Pattern) (ha : d15428 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34351 q ha hb
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34353 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15426 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15427 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15428 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34356 (p : Pattern) (ha : d15434 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15424 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34354 q ha hb
    | true =>
      simp only [d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15425 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15429 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34355 q ha hb
    | true =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15430 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15431 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15432 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15433 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15434 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34357 (p : Pattern) (ha : d15447 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15429 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34355 q ha hb
    | true =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15430 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34326 q ha hb
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15444 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15445 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15446 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15447 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34358 (p : Pattern) (ha : d13516 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1870 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1871 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1871, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1877 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1877, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13516 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34359 (p : Pattern) (ha : d15504 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34351 q ha hb
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34353 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15499 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34358 q ha hb
  have h9 (q : Pattern) (ha : d15500 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15501 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15502 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15503 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15504 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34360 (p : Pattern) (ha : d15510 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15505 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34359 q ha hb
    | true =>
      simp only [d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15506 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15507 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15508 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15509 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15510 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34361 (p : Pattern) (ha : d125639 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15448 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34356 q ha hb
    | true =>
      simp only [d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34357 q ha hb
  have h2 (q : Pattern) (ha : d125635 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15511 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34360 q ha hb
    | true =>
      simp only [d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15512 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34362 (p : Pattern) (ha : d125645 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15198 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34315 q ha hb
  have h2 (q : Pattern) (ha : d15199 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15208 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34315 q ha hb
    | true =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34318 q ha hb
  have h4 (q : Pattern) (ha : d15209 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15210 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125623 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34340 q ha hb
    | true =>
      simp only [d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34348 q ha hb
  have h7 (q : Pattern) (ha : d15365 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34321 q ha hb
    | true =>
      simp only [d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34322 q ha hb
  have h8 (q : Pattern) (ha : d125624 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125625 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125626 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125630 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34349 q ha hb
  have h12 (q : Pattern) (ha : d15374 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34323 q ha hb
  have h13 (q : Pattern) (ha : d125631 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125632 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125633 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125634 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125640 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34361 q ha hb
  have h18 (q : Pattern) (ha : d15528 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34328 q ha hb
  have h19 (q : Pattern) (ha : d125641 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125642 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125643 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125644 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125645 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34363 (p : Pattern) (ha : d125651 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34362 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34364 (p : Pattern) (ha : d15546 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2037 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2038 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2038, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15544 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15544, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15544, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13675 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13676 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d13676, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15545 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15545, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15546 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34365 (p : Pattern) (ha : d15551 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2056 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2056, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15547 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15547, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15547, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15548 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15549 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15549, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15550 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15550, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15551 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34366 (p : Pattern) (ha : d15558 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5249 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5250 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5250, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5251 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5251, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15555 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15556 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15556, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15557 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15557, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15558 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34367 (p : Pattern) (ha : d15563 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2068 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2068, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2071 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2071, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15555 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15556 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15556, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15557 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15557, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34368 (p : Pattern) (ha : d15569 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34364 q ha hb
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34366 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15564 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34367 q ha hb
  have h9 (q : Pattern) (ha : d15565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15568 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15569 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34369 (p : Pattern) (ha : d15573 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15564 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34367 q ha hb
  have h2 (q : Pattern) (ha : d15565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15573 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34370 (p : Pattern) (ha : d15579 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34368 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15579 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34371 (p : Pattern) (ha : d15583 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15583 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34372 (p : Pattern) (ha : d15589 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34370 q ha hb
    | true =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34371 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15589 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34373 (p : Pattern) (ha : d15592 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34368 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15592 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34374 (p : Pattern) (ha : d15593 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15593 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34375 (p : Pattern) (ha : d15599 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34370 q ha hb
    | true =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34371 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15594 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34373 q ha hb
    | true =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34374 q ha hb
  have h7 (q : Pattern) (ha : d15595 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15596 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34376 (p : Pattern) (ha : d15636 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34364 q ha hb
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34366 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15634 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15635 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15636 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34377 (p : Pattern) (ha : d15646 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34376 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15646 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34378 (p : Pattern) (ha : d15746 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15736 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34377 q ha hb
    | true =>
      simp only [d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34371 q ha hb
  have h2 (q : Pattern) (ha : d15737 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15738 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15739 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15740 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15741 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34371 q ha hb
    | true =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15742 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15743 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15744 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15745 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15746 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34379 (p : Pattern) (ha : d15752 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15741 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34371 q ha hb
    | true =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15742 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15743 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15744 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15745 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15747 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34374 q ha hb
    | true =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15748 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15749 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15750 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15751 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15752 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34380 (p : Pattern) (ha : d15761 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15747 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34374 q ha hb
    | true =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15748 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15749 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15750 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15751 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15761 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34381 (p : Pattern) (ha : d15786 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2343 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2343, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15785 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15785, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15785, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15777 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15778 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15778, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15779 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15779, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15786 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34382 (p : Pattern) (ha : d15813 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2349 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2355, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15792 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15793 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15793, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15794 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15794, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15813 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34383 (p : Pattern) (ha : d15819 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15814 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34382 q ha hb
  have h2 (q : Pattern) (ha : d15815 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15816 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15817 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15818 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15819 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34384 (p : Pattern) (ha : d15899 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15820 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34383 q ha hb
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15821 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15896 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15897 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15898 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15899 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34385 (p : Pattern) (ha : d15905 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15900 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34384 q ha hb
    | true =>
      simp only [d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15901 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15902 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15903 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15904 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15905 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34386 (p : Pattern) (ha : d15604 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34368 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34387 (p : Pattern) (ha : d15606 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15606 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34388 (p : Pattern) (ha : d15613 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34368 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15613 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34389 (p : Pattern) (ha : d15616 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15616 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34390 (p : Pattern) (ha : d15621 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2147 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2147, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15620 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15620, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15620, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15621 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34391 (p : Pattern) (ha : d15625 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13675 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13676 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13676, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15545 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15545, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15548 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15549 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15549, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15550 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15550, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15625 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34392 (p : Pattern) (ha : d15631 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15622 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34390 q ha hb
    | true =>
      simp only [d15622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34364 q ha hb
  have h2 (q : Pattern) (ha : d15623 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15624 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15626 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34364 q ha hb
    | true =>
      simp only [d15626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34391 q ha hb
  have h5 (q : Pattern) (ha : d15627 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15628 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15629 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15552 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34364 q ha hb
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
  have h9 (q : Pattern) (ha : d15553 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15554 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34366 q ha hb
  have h12 (q : Pattern) (ha : d15560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15630 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15631 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34393 (p : Pattern) (ha : d15642 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34392 q ha hb
    | true =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34376 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15642 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34394 (p : Pattern) (ha : d13614 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2068 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2068, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2071 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2071, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13614 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34395 (p : Pattern) (ha : d15697 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34364 q ha hb
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34366 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15692 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34365 q ha hb
    | true =>
      simp only [d15692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34394 q ha hb
  have h9 (q : Pattern) (ha : d15693 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15694 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15695 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15696 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15697 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34396 (p : Pattern) (ha : d15703 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34395 q ha hb
    | true =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15703 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34397 (p : Pattern) (ha : d125660 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34386 q ha hb
    | true =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34387 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34388 q ha hb
    | true =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34389 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34393 q ha hb
    | true =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34377 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34396 q ha hb
    | true =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125660 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34398 (p : Pattern) (ha : d15710 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34368 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15710 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34399 (p : Pattern) (ha : d15711 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15711 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34400 (p : Pattern) (ha : d15716 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34368 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15716 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34401 (p : Pattern) (ha : d15717 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15717 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34402 (p : Pattern) (ha : d15721 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34392 q ha hb
    | true =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34376 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15721 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34403 (p : Pattern) (ha : d15722 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34376 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34369 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15722 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34404 (p : Pattern) (ha : d15728 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34395 q ha hb
    | true =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15728 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34405 (p : Pattern) (ha : d125665 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34386 q ha hb
    | true =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34387 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34388 q ha hb
    | true =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34389 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34393 q ha hb
    | true =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34377 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34396 q ha hb
    | true =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15712 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34398 q ha hb
    | true =>
      simp only [d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34399 q ha hb
  have h16 (q : Pattern) (ha : d15713 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15714 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15715 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15718 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34400 q ha hb
    | true =>
      simp only [d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34401 q ha hb
  have h20 (q : Pattern) (ha : d15719 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15720 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15723 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34402 q ha hb
    | true =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34403 q ha hb
  have h23 (q : Pattern) (ha : d125661 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15729 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34404 q ha hb
    | true =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15730 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125663 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125664 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125665 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34406 (p : Pattern) (ha : d125672 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15723 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34402 q ha hb
    | true =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34403 q ha hb
  have h2 (q : Pattern) (ha : d125661 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15729 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34404 q ha hb
    | true =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15730 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125670 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125671 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34407 (p : Pattern) (ha : d15768 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2333 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2334 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2334, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15767 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15767, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15767, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15768 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34408 (p : Pattern) (ha : d15771 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2337 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2338 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2338, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15769 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15769, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15769, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13815 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d13816, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15770 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15770, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15771 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34409 (p : Pattern) (ha : d15780 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13816 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13816, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15770 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15770, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15777 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15778 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15778, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15779 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15779, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15780 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34410 (p : Pattern) (ha : d15795 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6645 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6646 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6646, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6647 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6647, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15792 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15793 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15793, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d15794 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15794, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d15795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34411 (p : Pattern) (ha : d15801 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15772 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34407 q ha hb
    | true =>
      simp only [d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34408 q ha hb
  have h2 (q : Pattern) (ha : d15773 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15774 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15781 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34408 q ha hb
    | true =>
      simp only [d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34409 q ha hb
  have h5 (q : Pattern) (ha : d15782 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15783 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15784 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15787 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34408 q ha hb
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
  have h9 (q : Pattern) (ha : d15788 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34410 q ha hb
  have h12 (q : Pattern) (ha : d15797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15798 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15800 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15801 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34412 (p : Pattern) (ha : d15806 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34408 q ha hb
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34410 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15804 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15805 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15806 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34413 (p : Pattern) (ha : d15812 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15802 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34411 q ha hb
    | true =>
      simp only [d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15803 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15807 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34412 q ha hb
    | true =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15808 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15809 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15810 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15811 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15812 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34414 (p : Pattern) (ha : d15825 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15807 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34412 q ha hb
    | true =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15808 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34383 q ha hb
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15822 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15823 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15824 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15825 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34415 (p : Pattern) (ha : d13843 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2349 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2355, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13843 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34416 (p : Pattern) (ha : d15882 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34408 q ha hb
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34410 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15877 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34415 q ha hb
  have h9 (q : Pattern) (ha : d15878 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15879 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15880 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15881 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15882 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34417 (p : Pattern) (ha : d15888 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15883 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34416 q ha hb
    | true =>
      simp only [d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15884 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15885 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15886 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15887 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15888 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34418 (p : Pattern) (ha : d125682 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15826 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34413 q ha hb
    | true =>
      simp only [d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34414 q ha hb
  have h2 (q : Pattern) (ha : d125678 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15889 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34417 q ha hb
    | true =>
      simp only [d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15890 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34419 (p : Pattern) (ha : d125688 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15590 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34372 q ha hb
  have h2 (q : Pattern) (ha : d15591 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34372 q ha hb
    | true =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34375 q ha hb
  have h4 (q : Pattern) (ha : d15601 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15602 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125666 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34397 q ha hb
    | true =>
      simp only [d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34405 q ha hb
  have h7 (q : Pattern) (ha : d15753 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34378 q ha hb
    | true =>
      simp only [d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34379 q ha hb
  have h8 (q : Pattern) (ha : d125667 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125668 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125669 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125673 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34406 q ha hb
  have h12 (q : Pattern) (ha : d15762 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34380 q ha hb
  have h13 (q : Pattern) (ha : d125674 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125675 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125676 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125677 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125683 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34418 q ha hb
  have h18 (q : Pattern) (ha : d15906 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34385 q ha hb
  have h19 (q : Pattern) (ha : d125684 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125685 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125686 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125687 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125688 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34420 (p : Pattern) (ha : d125694 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34419 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34421 (p : Pattern) (ha : d125700 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34161 q ha hb
    | true =>
      simp only [d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34249 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34306 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34363 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34420 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro34422 (p : Pattern) (ha : d125706 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34421 q ha hb
    | true =>
      simp only [d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34423 (p : Pattern) (ha : d125712 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34422 q ha hb
    | true =>
      simp only [d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34424 (p : Pattern) (ha : d125718 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34423 q ha hb
    | true =>
      simp only [d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34425 (p : Pattern) (ha : d125724 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34424 q ha hb
    | true =>
      simp only [d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34426 (p : Pattern) (ha : d125730 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34425 q ha hb
    | true =>
      simp only [d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34427 (p : Pattern) (ha : d125736 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34426 q ha hb
    | true =>
      simp only [d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34428 (p : Pattern) (ha : d125742 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34427 q ha hb
    | true =>
      simp only [d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34429 (p : Pattern) (ha : d0 p = 1) (hb : d166201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d166201 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro34430 (p : Pattern) (ha : d53647 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34118 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34119 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34137 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34138 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34431 (p : Pattern) (ha : d163447 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34129 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
  have h2 (q : Pattern) (ha : d14057 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14058 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14059 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14060 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163447 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34432 (p : Pattern) (ha : d163457 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34134 q ha hb
    | true =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34115 q ha hb
  have h2 (q : Pattern) (ha : d163453 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163454 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163455 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163456 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163457 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34433 (p : Pattern) (ha : d163463 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34139 q ha hb
    | true =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34140 q ha hb
  have h2 (q : Pattern) (ha : d14063 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163445 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163446 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163448 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34431 q ha hb
  have h6 (q : Pattern) (ha : d163449 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163450 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163451 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163452 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163458 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34432 q ha hb
  have h11 (q : Pattern) (ha : d163459 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163460 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163461 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163462 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163463 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34434 (p : Pattern) (ha : d163469 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34430 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163464 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34433 q ha hb
  have h7 (q : Pattern) (ha : d163465 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d163466 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d163467 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163468 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d163469 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34435 (p : Pattern) (ha : d163472 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14235 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34167 q ha hb
    | true =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34168 q ha hb
  have h2 (q : Pattern) (ha : d14236 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14237 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14238 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14239 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163472 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34436 (p : Pattern) (ha : d163483 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34199 q ha hb
    | true =>
      simp only [d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34174 q ha hb
  have h2 (q : Pattern) (ha : d163479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163480 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163481 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34437 (p : Pattern) (ha : d163489 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34166 q ha hb
    | true =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34169 q ha hb
  have h2 (q : Pattern) (ha : d14242 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163470 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163471 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163473 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34435 q ha hb
  have h6 (q : Pattern) (ha : d163474 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163475 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163476 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163477 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34436 q ha hb
  have h11 (q : Pattern) (ha : d163485 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163486 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163487 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163489 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34438 (p : Pattern) (ha : d163495 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163490 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34437 q ha hb
  have h2 (q : Pattern) (ha : d163491 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163492 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163493 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163494 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163495 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34439 (p : Pattern) (ha : d163499 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14502 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34211 q ha hb
    | true =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34212 q ha hb
  have h2 (q : Pattern) (ha : d14503 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14504 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14505 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14506 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163499 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34440 (p : Pattern) (ha : d163510 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163505 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34245 q ha hb
    | true =>
      simp only [d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34220 q ha hb
  have h2 (q : Pattern) (ha : d163506 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163507 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163508 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163509 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163510 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34441 (p : Pattern) (ha : d163516 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34210 q ha hb
    | true =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34213 q ha hb
  have h2 (q : Pattern) (ha : d14509 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163497 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163498 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163500 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34439 q ha hb
  have h6 (q : Pattern) (ha : d163501 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163502 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163503 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163504 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163511 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34440 q ha hb
  have h11 (q : Pattern) (ha : d163512 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163513 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163514 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163515 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163516 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34442 (p : Pattern) (ha : d163522 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163517 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34441 q ha hb
  have h2 (q : Pattern) (ha : d163518 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163519 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163520 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163521 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163522 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34443 (p : Pattern) (ha : d163527 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14809 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34259 q ha hb
    | true =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34260 q ha hb
  have h2 (q : Pattern) (ha : d14810 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14811 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14812 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14813 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163527 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34444 (p : Pattern) (ha : d163534 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34294 q ha hb
    | true =>
      simp only [d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34296 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15043 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34267 q ha hb
    | true =>
      simp only [d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34268 q ha hb
  have h9 (q : Pattern) (ha : d15044 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15045 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15046 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163533 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163534 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34445 (p : Pattern) (ha : d163540 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163535 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34444 q ha hb
    | true =>
      simp only [d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163536 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34269 q ha hb
    | true =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163537 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163538 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163539 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163540 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34446 (p : Pattern) (ha : d163546 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163541 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34445 q ha hb
    | true =>
      simp only [d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34270 q ha hb
  have h2 (q : Pattern) (ha : d163542 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163543 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163544 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163545 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163546 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34447 (p : Pattern) (ha : d163552 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34258 q ha hb
    | true =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34261 q ha hb
  have h2 (q : Pattern) (ha : d14816 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163525 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163526 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163528 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34443 q ha hb
  have h6 (q : Pattern) (ha : d163529 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163530 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163531 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163532 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163547 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34446 q ha hb
  have h11 (q : Pattern) (ha : d163548 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163549 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163550 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163551 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163552 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34448 (p : Pattern) (ha : d163558 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163553 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34447 q ha hb
  have h2 (q : Pattern) (ha : d163554 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163555 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163556 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163557 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163558 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34449 (p : Pattern) (ha : d163564 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15202 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34316 q ha hb
    | true =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34317 q ha hb
  have h2 (q : Pattern) (ha : d15203 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15204 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15205 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15206 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163564 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34450 (p : Pattern) (ha : d163571 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34351 q ha hb
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34353 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15436 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34324 q ha hb
    | true =>
      simp only [d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34325 q ha hb
  have h9 (q : Pattern) (ha : d15437 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15438 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15439 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34451 (p : Pattern) (ha : d163577 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34450 q ha hb
    | true =>
      simp only [d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163573 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34326 q ha hb
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34452 (p : Pattern) (ha : d163583 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163578 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34451 q ha hb
    | true =>
      simp only [d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34327 q ha hb
  have h2 (q : Pattern) (ha : d163579 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163583 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34453 (p : Pattern) (ha : d163589 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34315 q ha hb
    | true =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34318 q ha hb
  have h2 (q : Pattern) (ha : d15209 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34449 q ha hb
  have h6 (q : Pattern) (ha : d163566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163568 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163569 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34452 q ha hb
  have h11 (q : Pattern) (ha : d163585 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163589 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34454 (p : Pattern) (ha : d163595 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163590 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34453 q ha hb
  have h2 (q : Pattern) (ha : d163591 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163592 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163593 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163594 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163595 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34455 (p : Pattern) (ha : d163602 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15594 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34373 q ha hb
    | true =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34374 q ha hb
  have h2 (q : Pattern) (ha : d15595 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15596 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163602 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34456 (p : Pattern) (ha : d163609 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34408 q ha hb
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34410 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15814 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34381 q ha hb
    | true =>
      simp only [d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34382 q ha hb
  have h9 (q : Pattern) (ha : d15815 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15816 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15817 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163608 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34457 (p : Pattern) (ha : d163615 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163610 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34456 q ha hb
    | true =>
      simp only [d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163611 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34383 q ha hb
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163612 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163613 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163614 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163615 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34458 (p : Pattern) (ha : d163621 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163616 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34457 q ha hb
    | true =>
      simp only [d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34384 q ha hb
  have h2 (q : Pattern) (ha : d163617 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163620 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163621 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34459 (p : Pattern) (ha : d163627 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34372 q ha hb
    | true =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34375 q ha hb
  have h2 (q : Pattern) (ha : d15601 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163601 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34455 q ha hb
  have h6 (q : Pattern) (ha : d163604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163605 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163606 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163607 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163622 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34458 q ha hb
  have h11 (q : Pattern) (ha : d163623 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163624 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163625 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163626 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163627 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34460 (p : Pattern) (ha : d163633 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163628 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34459 q ha hb
  have h2 (q : Pattern) (ha : d163629 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163630 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163631 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163632 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163633 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34461 (p : Pattern) (ha : d163639 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d163496 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34434 q ha hb
    | true =>
      simp only [d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34438 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d163523 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34442 q ha hb
  have h3 (q : Pattern) (ha : d163524 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34448 q ha hb
  have h5 (q : Pattern) (ha : d163560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d163596 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34454 q ha hb
  have h8 (q : Pattern) (ha : d163597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d163598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d163634 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34460 q ha hb
  have h12 (q : Pattern) (ha : d163635 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163636 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d163637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d163638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d163639 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro34462 (p : Pattern) (ha : d163645 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163640 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34461 q ha hb
    | true =>
      simp only [d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163641 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163642 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163643 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163644 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163645 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34463 (p : Pattern) (ha : d163651 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163646 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34462 q ha hb
    | true =>
      simp only [d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163647 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163648 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163649 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34464 (p : Pattern) (ha : d163657 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34463 q ha hb
    | true =>
      simp only [d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163653 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163654 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163655 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163656 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163657 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34465 (p : Pattern) (ha : d163663 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163658 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34464 q ha hb
    | true =>
      simp only [d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163659 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163660 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163661 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163663 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34466 (p : Pattern) (ha : d163669 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163664 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34465 q ha hb
    | true =>
      simp only [d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163665 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163666 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163667 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163668 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163669 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34467 (p : Pattern) (ha : d163675 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163670 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34466 q ha hb
    | true =>
      simp only [d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163671 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163672 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163673 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163674 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163675 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34468 (p : Pattern) (ha : d163681 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163676 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34467 q ha hb
    | true =>
      simp only [d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163677 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163678 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163679 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163680 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163681 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34469 (p : Pattern) (ha : d0 p = 1) (hb : d166468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d166468 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro34470 (p : Pattern) (ha : d13981 p = 1) (hb : d122305 p = 1) : d123879 p = 1 := by
  have h0 (q : Pattern) (ha : d13980 q = 1) (hb : d122304 q = 1) : d13980 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13981 q = 1) (hb : d122305 q = 1) : d123879 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13981, d122305, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13981, d122305, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34471 (p : Pattern) (ha : d13987 p = 1) (hb : d122305 p = 1) : d158538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d122305 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13985 q = 1) (hb : d122305 q = 1) : d158536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13985, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d122305 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13986 q = 1) (hb : d122305 q = 1) : d158537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, d158537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13986, d158537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13987 q = 1) (hb : d122305 q = 1) : d158538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, d158538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13987, d158538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro34472 (p : Pattern) (ha : d13993 p = 1) (hb : d122305 p = 1) : d158544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13992 q = 1) (hb : d122305 q = 1) : d158543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13992, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13993 q = 1) (hb : d122305 q = 1) : d158544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, d158544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13993, d158544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro34473 (p : Pattern) (ha : d122305 p = 1) (hb : d125417 p = 1) : d158550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d122305 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d122305 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13994 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
    | true =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125413 q = 1) : d158546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125413, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122305 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125414 q = 1) : d158547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125414, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125415 q = 1) : d158548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125415, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125416 q = 1) : d158549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125416, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125417 q = 1) : d158550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125417, d158550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125417, d158550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34474 (p : Pattern) (ha : d14000 p = 1) (hb : d122305 p = 1) : d158551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13992 q = 1) (hb : d122305 q = 1) : d158543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13992, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14000 q = 1) (hb : d122305 q = 1) : d158551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, d158551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14000, d158551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34475 (p : Pattern) (ha : d122305 p = 1) (hb : d125422 p = 1) : d158557 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d122305 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d122305 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13994 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
    | true =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125413 q = 1) : d158546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125413, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122305 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125414 q = 1) : d158547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125414, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125415 q = 1) : d158548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125415, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125416 q = 1) : d158549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125416, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d122305 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d122305 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14001 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34474 q ha hb
    | true =>
      simp only [d14001, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125418 q = 1) : d158553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d125418, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d122305 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125419 q = 1) : d158554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125419, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125420 q = 1) : d158555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125420, d158555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125420, d158555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122305 q = 1) (hb : d125421 q = 1) : d158556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125421, d158556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125421, d158556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d122305 q = 1) (hb : d125422 q = 1) : d158557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125422, d158557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125422, d158557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34476 (p : Pattern) (ha : d122305 p = 1) (hb : d125429 p = 1) : d158564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14001 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34474 q ha hb
    | true =>
      simp only [d14001, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125418 q = 1) : d158553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125418, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d122305 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125419 q = 1) : d158554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125419, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125427 q = 1) : d158562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125427, d158562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125427, d158562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125428 q = 1) : d158563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125428, d158563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125428, d158563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125429 q = 1) : d158564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125429, d158564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125429, d158564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34477 (p : Pattern) (ha : d14020 p = 1) (hb : d122305 p = 1) : d123917 p = 1 := by
  have h0 (q : Pattern) (ha : d14019 q = 1) (hb : d122304 q = 1) : d14019 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14020 q = 1) (hb : d122305 q = 1) : d123917 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14020, d122305, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14020, d122305, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34478 (p : Pattern) (ha : d14026 p = 1) (hb : d122305 p = 1) : d158572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d122305 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14024 q = 1) (hb : d122305 q = 1) : d158570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14024, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d122305 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14025 q = 1) (hb : d122305 q = 1) : d158571 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, d158571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14025, d158571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14026 q = 1) (hb : d122305 q = 1) : d158572 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, d158572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14026, d158572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro34479 (p : Pattern) (ha : d14032 p = 1) (hb : d122305 p = 1) : d158578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d122305 q = 1) : d158573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34478 q ha hb
    | true =>
      simp only [d14027, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d122305 q = 1) : d158574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d122305 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14029 q = 1) (hb : d122305 q = 1) : d158575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, d158575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14029, d158575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14030 q = 1) (hb : d122305 q = 1) : d158576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, d158576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14030, d158576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14031 q = 1) (hb : d122305 q = 1) : d158577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, d158577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14031, d158577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14032 q = 1) (hb : d122305 q = 1) : d158578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, d158578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14032, d158578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34480 (p : Pattern) (ha : d122305 p = 1) (hb : d125439 p = 1) : d158584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122305 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14033 q = 1) (hb : d122305 q = 1) : d158579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34479 q ha hb
    | true =>
      simp only [d14033, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125435 q = 1) : d158580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125435, d158580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125435, d158580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d122305 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125436 q = 1) : d158581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125436, d158581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125436, d158581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125437 q = 1) : d158582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125437, d158582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125437, d158582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125438 q = 1) : d158583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125438, d158583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125438, d158583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125439 q = 1) : d158584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125439, d158584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125439, d158584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34481 (p : Pattern) (ha : d122305 p = 1) (hb : d125445 p = 1) : d158590 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d122305 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d125423 q = 1) : d158558 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125423, d158558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34473 q ha hb
    | true =>
      simp only [d125423, d158558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34475 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d122305 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125424 q = 1) : d158559 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125424, d158559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125424, d158559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125425 q = 1) : d158560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125425, d158560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125425, d158560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125426 q = 1) : d158561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125426, d158561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125426, d158561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125430 q = 1) : d158565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125430, d158565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125430, d158565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34476 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125431 q = 1) : d158566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125431, d158566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125431, d158566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125432 q = 1) : d158567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125432, d158567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125432, d158567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125433 q = 1) : d158568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125433, d158568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125433, d158568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125434 q = 1) : d158569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125434, d158569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125434, d158569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125440 q = 1) : d158585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125440, d158585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125440, d158585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34480 q ha hb
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125441 q = 1) : d158586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125441, d158586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125441, d158586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125442 q = 1) : d158587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125442, d158587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125442, d158587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125443 q = 1) : d158588 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125443, d158588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125443, d158588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125444 q = 1) : d158589 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125444, d158589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125444, d158589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125445 q = 1) : d158590 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125445, d158590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125445, d158590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro34482 (p : Pattern) (ha : d14054 p = 1) (hb : d122305 p = 1) : d158600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13994 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
    | true =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14050 q = 1) (hb : d122305 q = 1) : d158596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14051 q = 1) (hb : d122305 q = 1) : d158597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14051, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14052 q = 1) (hb : d122305 q = 1) : d158598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14053 q = 1) (hb : d122305 q = 1) : d158599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14054 q = 1) (hb : d122305 q = 1) : d158600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro34483 (p : Pattern) (ha : d14061 p = 1) (hb : d122305 p = 1) : d158607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13994 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
    | true =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14050 q = 1) (hb : d122305 q = 1) : d158596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14051 q = 1) (hb : d122305 q = 1) : d158597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14051, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14052 q = 1) (hb : d122305 q = 1) : d158598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14053 q = 1) (hb : d122305 q = 1) : d158599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14001 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34474 q ha hb
    | true =>
      simp only [d14001, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14057 q = 1) (hb : d122305 q = 1) : d158603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14058 q = 1) (hb : d122305 q = 1) : d158604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14058, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14059 q = 1) (hb : d122305 q = 1) : d158605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14060 q = 1) (hb : d122305 q = 1) : d158606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14061 q = 1) (hb : d122305 q = 1) : d158607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14061, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro34484 (p : Pattern) (ha : d14141 p = 1) (hb : d122305 p = 1) : d158664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13994 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
    | true =>
      simp only [d13994, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14050 q = 1) (hb : d122305 q = 1) : d158596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14051 q = 1) (hb : d122305 q = 1) : d158597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14051, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14052 q = 1) (hb : d122305 q = 1) : d158598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14053 q = 1) (hb : d122305 q = 1) : d158599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d122305 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14141 q = 1) (hb : d122305 q = 1) : d158664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, d158664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14141, d158664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34485 (p : Pattern) (ha : d14066 p = 1) (hb : d122305 p = 1) : d158612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14065 q = 1) (hb : d122305 q = 1) : d158611 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14066 q = 1) (hb : d122305 q = 1) : d158612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, d158612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14066, d158612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro34486 (p : Pattern) (ha : d14073 p = 1) (hb : d122305 p = 1) : d158619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14071 q = 1) (hb : d122305 q = 1) : d158617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14072 q = 1) (hb : d122305 q = 1) : d158618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14072, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14073 q = 1) (hb : d122305 q = 1) : d158619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, d158619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14073, d158619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro34487 (p : Pattern) (ha : d14079 p = 1) (hb : d122305 p = 1) : d123974 p = 1 := by
  have h0 (q : Pattern) (ha : d14077 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14079 q = 1) (hb : d122305 q = 1) : d123974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14079, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14079, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34488 (p : Pattern) (ha : d14085 p = 1) (hb : d122305 p = 1) : d158625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
    | true =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14083 q = 1) (hb : d122305 q = 1) : d158623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d122305 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13985 q = 1) (hb : d122305 q = 1) : d158536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13985, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14084 q = 1) (hb : d122305 q = 1) : d158624 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, d158624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14084, d158624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14085 q = 1) (hb : d122305 q = 1) : d158625 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, d158625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14085, d158625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro34489 (p : Pattern) (ha : d14091 p = 1) (hb : d122305 p = 1) : d158631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d122305 q = 1) : d158626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34488 q ha hb
    | true =>
      simp only [d14086, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d122305 q = 1) : d158627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d122305 q = 1) : d158628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d122305 q = 1) : d158629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d122305 q = 1) : d158630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14091 q = 1) (hb : d122305 q = 1) : d158631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, d158631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14091, d158631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34490 (p : Pattern) (ha : d14112 p = 1) (hb : d122305 p = 1) : d158637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d122305 q = 1) : d158634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d122305 q = 1) : d158635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d122305 q = 1) : d158636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14112 q = 1) (hb : d122305 q = 1) : d158637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, d158637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14112, d158637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34491 (p : Pattern) (ha : d122305 p = 1) (hb : d125455 p = 1) : d158643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122305 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14067 q = 1) (hb : d122305 q = 1) : d158613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34485 q ha hb
    | true =>
      simp only [d14067, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14068 q = 1) (hb : d122305 q = 1) : d158614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14069 q = 1) (hb : d122305 q = 1) : d158615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14069, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14070 q = 1) (hb : d122305 q = 1) : d158616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122305 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14074 q = 1) (hb : d122305 q = 1) : d158620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34486 q ha hb
    | true =>
      simp only [d14074, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14075 q = 1) (hb : d122305 q = 1) : d158621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14076 q = 1) (hb : d122305 q = 1) : d158622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14076, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14092 q = 1) (hb : d122305 q = 1) : d158632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34489 q ha hb
    | true =>
      simp only [d14092, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125451 q = 1) : d158633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125451, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14113 q = 1) (hb : d122305 q = 1) : d158638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34490 q ha hb
    | true =>
      simp only [d14113, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d14114 q = 1) (hb : d122305 q = 1) : d158639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14114, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125452 q = 1) : d158640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125452, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125453 q = 1) : d158641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125453, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125454 q = 1) : d158642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125454, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125455 q = 1) : d158643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, d158643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125455, d158643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro34492 (p : Pattern) (ha : d14119 p = 1) (hb : d122305 p = 1) : d158644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14065 q = 1) (hb : d122305 q = 1) : d158611 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14119 q = 1) (hb : d122305 q = 1) : d158644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, d158644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14119, d158644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34493 (p : Pattern) (ha : d14124 p = 1) (hb : d122305 p = 1) : d158649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14071 q = 1) (hb : d122305 q = 1) : d158617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14072 q = 1) (hb : d122305 q = 1) : d158618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14072, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14124 q = 1) (hb : d122305 q = 1) : d158649 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14124, d158649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14124, d158649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34494 (p : Pattern) (ha : d14128 p = 1) (hb : d122305 p = 1) : d158653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d122305 q = 1) : d158626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34488 q ha hb
    | true =>
      simp only [d14086, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d122305 q = 1) : d158627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d122305 q = 1) : d158628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d122305 q = 1) : d158629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d122305 q = 1) : d158630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14128 q = 1) (hb : d122305 q = 1) : d158653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14128, d158653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14128, d158653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34495 (p : Pattern) (ha : d14133 p = 1) (hb : d122305 p = 1) : d158656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34471 q ha hb
    | true =>
      simp only [d13988, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d122305 q = 1) : d158634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d122305 q = 1) : d158635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d122305 q = 1) : d158636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14133 q = 1) (hb : d122305 q = 1) : d158656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14133, d158656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14133, d158656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34496 (p : Pattern) (ha : d122305 p = 1) (hb : d125460 p = 1) : d158662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122305 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14067 q = 1) (hb : d122305 q = 1) : d158613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34485 q ha hb
    | true =>
      simp only [d14067, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14068 q = 1) (hb : d122305 q = 1) : d158614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14069 q = 1) (hb : d122305 q = 1) : d158615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14069, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14070 q = 1) (hb : d122305 q = 1) : d158616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122305 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14074 q = 1) (hb : d122305 q = 1) : d158620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34486 q ha hb
    | true =>
      simp only [d14074, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14075 q = 1) (hb : d122305 q = 1) : d158621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14076 q = 1) (hb : d122305 q = 1) : d158622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14076, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14092 q = 1) (hb : d122305 q = 1) : d158632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34489 q ha hb
    | true =>
      simp only [d14092, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34472 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125451 q = 1) : d158633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125451, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14113 q = 1) (hb : d122305 q = 1) : d158638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34490 q ha hb
    | true =>
      simp only [d14113, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d14114 q = 1) (hb : d122305 q = 1) : d158639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14114, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125452 q = 1) : d158640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125452, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125453 q = 1) : d158641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125453, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125454 q = 1) : d158642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125454, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d122305 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d14120 q = 1) (hb : d122305 q = 1) : d158645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14120, d158645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34492 q ha hb
    | true =>
      simp only [d14120, d158645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14121 q = 1) (hb : d122305 q = 1) : d158646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14121, d158646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14121, d158646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14122 q = 1) (hb : d122305 q = 1) : d158647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14122, d158647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d14122, d158647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d14123 q = 1) (hb : d122305 q = 1) : d158648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14123, d158648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14123, d158648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d122305 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d14125 q = 1) (hb : d122305 q = 1) : d158650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14125, d158650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34493 q ha hb
    | true =>
      simp only [d14125, d158650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d14126 q = 1) (hb : d122305 q = 1) : d158651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14126, d158651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14126, d158651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d14127 q = 1) (hb : d122305 q = 1) : d158652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14127, d158652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14127, d158652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d14129 q = 1) (hb : d122305 q = 1) : d158654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34494 q ha hb
    | true =>
      simp only [d14129, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34474 q ha hb
  have h27 (q : Pattern) (ha : d122305 q = 1) (hb : d125456 q = 1) : d158655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d125456, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d14134 q = 1) (hb : d122305 q = 1) : d158657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34495 q ha hb
    | true =>
      simp only [d14134, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d14135 q = 1) (hb : d122305 q = 1) : d158658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d14135, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d122305 q = 1) (hb : d125457 q = 1) : d158659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d125457, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d122305 q = 1) (hb : d125458 q = 1) : d158660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, d158660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d125458, d158660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d122305 q = 1) (hb : d125459 q = 1) : d158661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, d158661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125459, d158661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d122305 q = 1) (hb : d125460 q = 1) : d158662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, d158662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125460, d158662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro34497 (p : Pattern) (ha : d122305 p = 1) (hb : d125467 p = 1) : d158671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14129 q = 1) (hb : d122305 q = 1) : d158654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34494 q ha hb
    | true =>
      simp only [d14129, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34474 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125456 q = 1) : d158655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125456, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14134 q = 1) (hb : d122305 q = 1) : d158657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34495 q ha hb
    | true =>
      simp only [d14134, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14135 q = 1) (hb : d122305 q = 1) : d158658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14135, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125457 q = 1) : d158659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125457, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125465 q = 1) : d158669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, d158669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125465, d158669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125466 q = 1) : d158670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, d158670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125466, d158670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125467 q = 1) : d158671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, d158671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125467, d158671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34498 (p : Pattern) (ha : d14156 p = 1) (hb : d122305 p = 1) : d124032 p = 1 := by
  have h0 (q : Pattern) (ha : d14154 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14156 q = 1) (hb : d122305 q = 1) : d124032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14156, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14156, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34499 (p : Pattern) (ha : d14162 p = 1) (hb : d122305 p = 1) : d158679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14157 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
    | true =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
  have h2 (q : Pattern) (ha : d14158 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14159 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14160 q = 1) (hb : d122305 q = 1) : d158677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14160, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d122305 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14024 q = 1) (hb : d122305 q = 1) : d158570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14024, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14161 q = 1) (hb : d122305 q = 1) : d158678 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14161, d158678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14161, d158678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14162 q = 1) (hb : d122305 q = 1) : d158679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14162, d158679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14162, d158679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
end NetHack.Soko22Hazard87
