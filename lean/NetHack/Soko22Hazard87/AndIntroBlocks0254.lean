import NetHack.Soko22Hazard87.AndIntroBlocks0253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro63500 (p : Pattern) (ha : d243575 p = 1) (hb : d252915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243569 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243568 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243570 q = 1) (hb : d252910 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243570, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243570, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63459 q ha hb
  have h4 (q : Pattern) (ha : d243365 q = 1) (hb : d252746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243365, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63459 q ha hb
    | true =>
      simp only [d243365, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d243571 q = 1) (hb : d252911 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243571, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243571, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243366 q = 1) (hb : d252747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243366, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243366, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d243572 q = 1) (hb : d252912 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243572, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243572, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243573 q = 1) (hb : d252913 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243573, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243573, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d243574 q = 1) (hb : d252914 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243574, d252914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243574, d252914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243575 q = 1) (hb : d252915 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243575, d252915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243575, d252915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63501 (p : Pattern) (ha : d243581 p = 1) (hb : d252921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243568 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243570 q = 1) (hb : d252910 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243570, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243570, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63459 q ha hb
  have h3 (q : Pattern) (ha : d243365 q = 1) (hb : d252746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243365, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63459 q ha hb
    | true =>
      simp only [d243365, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d243571 q = 1) (hb : d252911 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243571, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243571, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243366 q = 1) (hb : d252747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243366, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243366, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d243572 q = 1) (hb : d252912 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243572, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243572, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243573 q = 1) (hb : d252913 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243573, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243573, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d243574 q = 1) (hb : d252914 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243574, d252914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243574, d252914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243576 q = 1) (hb : d252916 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243576, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243576, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63460 q ha hb
  have h10 (q : Pattern) (ha : d243373 q = 1) (hb : d252752 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243373, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63460 q ha hb
    | true =>
      simp only [d243373, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d243577 q = 1) (hb : d252917 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243577, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243577, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243374 q = 1) (hb : d252753 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243374, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243374, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d243578 q = 1) (hb : d252918 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243578, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243578, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243579 q = 1) (hb : d252919 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243579, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243579, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d243580 q = 1) (hb : d252920 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243580, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243580, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243581 q = 1) (hb : d252921 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243581, d252921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243581, d252921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro63502 (p : Pattern) (ha : d243586 p = 1) (hb : d252926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243570 q = 1) (hb : d252910 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243570, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243570, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63459 q ha hb
  have h2 (q : Pattern) (ha : d243365 q = 1) (hb : d252746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243365, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63459 q ha hb
    | true =>
      simp only [d243365, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243571 q = 1) (hb : d252911 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243571, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243571, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243366 q = 1) (hb : d252747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243366, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243366, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243572 q = 1) (hb : d252912 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243572, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243572, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243573 q = 1) (hb : d252913 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243573, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243573, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243576 q = 1) (hb : d252916 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243576, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243576, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63460 q ha hb
  have h8 (q : Pattern) (ha : d243373 q = 1) (hb : d252752 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243373, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63460 q ha hb
    | true =>
      simp only [d243373, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243577 q = 1) (hb : d252917 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243577, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243577, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243374 q = 1) (hb : d252753 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243374, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243374, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243578 q = 1) (hb : d252918 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243578, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243578, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243579 q = 1) (hb : d252919 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243579, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243579, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243580 q = 1) (hb : d252920 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243580, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243580, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243585 q = 1) (hb : d252925 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243585, d252925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243585, d252925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243586 q = 1) (hb : d252926 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243586, d252926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243586, d252926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63503 (p : Pattern) (ha : d243600 p = 1) (hb : d252926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243591 q = 1) (hb : d252910 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243591, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243591, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63462 q ha hb
  have h2 (q : Pattern) (ha : d243385 q = 1) (hb : d252746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243385, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63462 q ha hb
    | true =>
      simp only [d243385, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243592 q = 1) (hb : d252911 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243592, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243592, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243386 q = 1) (hb : d252747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243386, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243386, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243593 q = 1) (hb : d252912 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243593, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243593, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243594 q = 1) (hb : d252913 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243594, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243594, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243595 q = 1) (hb : d252916 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243595, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243595, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63463 q ha hb
  have h8 (q : Pattern) (ha : d243390 q = 1) (hb : d252752 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243390, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63463 q ha hb
    | true =>
      simp only [d243390, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243596 q = 1) (hb : d252917 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243596, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243596, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243391 q = 1) (hb : d252753 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243391, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243391, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243597 q = 1) (hb : d252918 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243597, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243597, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243598 q = 1) (hb : d252919 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243598, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243598, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243599 q = 1) (hb : d252920 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243599, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243599, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243576 q = 1) (hb : d252916 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243576, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243576, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63460 q ha hb
  have h15 (q : Pattern) (ha : d243373 q = 1) (hb : d252752 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243373, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63460 q ha hb
    | true =>
      simp only [d243373, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243577 q = 1) (hb : d252917 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243577, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243577, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243374 q = 1) (hb : d252753 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243374, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243374, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d243578 q = 1) (hb : d252918 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243578, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243578, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d243579 q = 1) (hb : d252919 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243579, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d243579, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d243585 q = 1) (hb : d252925 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243585, d252925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243585, d252925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243600 q = 1) (hb : d252926 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243600, d252926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243600, d252926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro63504 (p : Pattern) (ha : d243605 p = 1) (hb : d252931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243595 q = 1) (hb : d252916 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243595, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243595, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63463 q ha hb
  have h2 (q : Pattern) (ha : d243390 q = 1) (hb : d252752 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243390, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63463 q ha hb
    | true =>
      simp only [d243390, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243596 q = 1) (hb : d252917 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243596, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243596, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243391 q = 1) (hb : d252753 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243391, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243391, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243597 q = 1) (hb : d252918 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243597, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243597, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243598 q = 1) (hb : d252919 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243598, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243598, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243604 q = 1) (hb : d252925 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243604, d252925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243604, d252925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
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
  have h15 (q : Pattern) (ha : d243605 q = 1) (hb : d252931 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243605, d252931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243605, d252931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro63505 (p : Pattern) (ha : d243611 p = 1) (hb : d252937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243582 q = 1) (hb : d252922 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243582, d252922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63500 q ha hb
    | true =>
      simp only [d243582, d252922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63501 q ha hb
  have h2 (q : Pattern) (ha : d243583 q = 1) (hb : d252923 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243583, d252923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243583, d252923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243584 q = 1) (hb : d252924 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243584, d252924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243584, d252924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243587 q = 1) (hb : d252927 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243587, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63501 q ha hb
    | true =>
      simp only [d243587, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63502 q ha hb
  have h5 (q : Pattern) (ha : d243588 q = 1) (hb : d252928 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243588, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243588, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243589 q = 1) (hb : d252929 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243589, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243589, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243590 q = 1) (hb : d252930 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243590, d252930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243590, d252930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243601 q = 1) (hb : d252927 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243601, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63501 q ha hb
    | true =>
      simp only [d243601, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
  have h9 (q : Pattern) (ha : d243602 q = 1) (hb : d252928 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243602, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243602, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243603 q = 1) (hb : d252929 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243603, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243603, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243606 q = 1) (hb : d252932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
    | true =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63504 q ha hb
  have h12 (q : Pattern) (ha : d243607 q = 1) (hb : d252933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243608 q = 1) (hb : d252934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243609 q = 1) (hb : d252935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243609, d252935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243609, d252935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243610 q = 1) (hb : d252936 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243610, d252936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243610, d252936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243611 q = 1) (hb : d252937 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243611, d252937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243611, d252937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro63506 (p : Pattern) (ha : d243616 p = 1) (hb : d252942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243601 q = 1) (hb : d252927 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243601, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63501 q ha hb
    | true =>
      simp only [d243601, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
  have h2 (q : Pattern) (ha : d243602 q = 1) (hb : d252928 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243602, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243602, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243603 q = 1) (hb : d252929 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243603, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243603, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243606 q = 1) (hb : d252932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
    | true =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63504 q ha hb
  have h5 (q : Pattern) (ha : d243607 q = 1) (hb : d252933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243608 q = 1) (hb : d252934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243609 q = 1) (hb : d252935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243609, d252935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243609, d252935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243614 q = 1) (hb : d252940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243614, d252940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243614, d252940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243615 q = 1) (hb : d252941 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243615, d252941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243615, d252941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243616 q = 1) (hb : d252942 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243616, d252942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243616, d252942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro63507 (p : Pattern) (ha : d243622 p = 1) (hb : d252948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243612 q = 1) (hb : d252938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243612, d252938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63505 q ha hb
    | true =>
      simp only [d243612, d252938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243613 q = 1) (hb : d252939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243613, d252939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243613, d252939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243617 q = 1) (hb : d252943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243617, d252943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63506 q ha hb
    | true =>
      simp only [d243617, d252943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243618 q = 1) (hb : d252944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243618, d252944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243618, d252944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243619 q = 1) (hb : d252945 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243619, d252945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243619, d252945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243620 q = 1) (hb : d252946 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243620, d252946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243620, d252946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243621 q = 1) (hb : d252947 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243621, d252947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243621, d252947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243622 q = 1) (hb : d252948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243622, d252948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243622, d252948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro63508 (p : Pattern) (ha : d243624 p = 1) (hb : d252950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243606 q = 1) (hb : d252932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
    | true =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63504 q ha hb
  have h2 (q : Pattern) (ha : d243607 q = 1) (hb : d252933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243608 q = 1) (hb : d252934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243614 q = 1) (hb : d252940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243614, d252940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243614, d252940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243623 q = 1) (hb : d252949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243623, d252949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243623, d252949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243624 q = 1) (hb : d252950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243624, d252950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243624, d252950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63509 (p : Pattern) (ha : d243630 p = 1) (hb : d252956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243617 q = 1) (hb : d252943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243617, d252943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63506 q ha hb
    | true =>
      simp only [d243617, d252943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243618 q = 1) (hb : d252944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243618, d252944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243618, d252944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243625 q = 1) (hb : d252951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243625, d252951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63508 q ha hb
    | true =>
      simp only [d243625, d252951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243626 q = 1) (hb : d252952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243626, d252952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243626, d252952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243627 q = 1) (hb : d252953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243627, d252953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243627, d252953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243628 q = 1) (hb : d252954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243628, d252954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243628, d252954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243629 q = 1) (hb : d252955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243629, d252955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243629, d252955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243630 q = 1) (hb : d252956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243630, d252956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243630, d252956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro63510 (p : Pattern) (ha : d243643 p = 1) (hb : d252964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243591 q = 1) (hb : d252910 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243591, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243591, d252910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63462 q ha hb
  have h2 (q : Pattern) (ha : d243385 q = 1) (hb : d252746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243385, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63462 q ha hb
    | true =>
      simp only [d243385, d252746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243592 q = 1) (hb : d252911 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243592, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243592, d252911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243386 q = 1) (hb : d252747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243386, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243386, d252747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243593 q = 1) (hb : d252912 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243593, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243593, d252912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243594 q = 1) (hb : d252913 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243594, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243594, d252913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243595 q = 1) (hb : d252916 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243595, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243595, d252916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63463 q ha hb
  have h8 (q : Pattern) (ha : d243390 q = 1) (hb : d252752 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243390, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63463 q ha hb
    | true =>
      simp only [d243390, d252752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243596 q = 1) (hb : d252917 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243596, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243596, d252917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243391 q = 1) (hb : d252753 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243391, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243391, d252753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243597 q = 1) (hb : d252918 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243597, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243597, d252918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243598 q = 1) (hb : d252919 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243598, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243598, d252919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243599 q = 1) (hb : d252920 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243599, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243599, d252920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243638 q = 1) (hb : d252959 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243638, d252959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243638, d252959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63482 q ha hb
  have h15 (q : Pattern) (ha : d243483 q = 1) (hb : d252837 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243483, d252837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63482 q ha hb
    | true =>
      simp only [d243483, d252837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243639 q = 1) (hb : d252960 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243639, d252960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243639, d252960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243484 q = 1) (hb : d252838 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243484, d252838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243484, d252838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d243640 q = 1) (hb : d252961 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243640, d252961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243640, d252961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d243641 q = 1) (hb : d252962 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243641, d252962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d243641, d252962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d243642 q = 1) (hb : d252963 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243642, d252963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243642, d252963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243643 q = 1) (hb : d252964 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243643, d252964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243643, d252964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro63511 (p : Pattern) (ha : d243649 p = 1) (hb : d252965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243644 q = 1) (hb : d252959 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243644, d252959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243644, d252959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63484 q ha hb
  have h2 (q : Pattern) (ha : d243493 q = 1) (hb : d252837 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243493, d252837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63484 q ha hb
    | true =>
      simp only [d243493, d252837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243645 q = 1) (hb : d252960 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243645, d252960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243645, d252960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243494 q = 1) (hb : d252838 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243494, d252838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243494, d252838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243646 q = 1) (hb : d252961 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243646, d252961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243646, d252961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243647 q = 1) (hb : d252962 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243647, d252962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243647, d252962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243648 q = 1) (hb : d252963 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243648, d252963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243648, d252963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243649 q = 1) (hb : d252965 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243649, d252965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243649, d252965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro63512 (p : Pattern) (ha : d243655 p = 1) (hb : d252971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243601 q = 1) (hb : d252927 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243601, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63501 q ha hb
    | true =>
      simp only [d243601, d252927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
  have h2 (q : Pattern) (ha : d243602 q = 1) (hb : d252928 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243602, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243602, d252928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243603 q = 1) (hb : d252929 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243603, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243603, d252929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243606 q = 1) (hb : d252932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63503 q ha hb
    | true =>
      simp only [d243606, d252932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63504 q ha hb
  have h5 (q : Pattern) (ha : d243607 q = 1) (hb : d252933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243607, d252933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243608 q = 1) (hb : d252934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243608, d252934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243609 q = 1) (hb : d252935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243609, d252935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243609, d252935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243650 q = 1) (hb : d252966 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243650, d252966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63510 q ha hb
    | true =>
      simp only [d243650, d252966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63511 q ha hb
  have h9 (q : Pattern) (ha : d243651 q = 1) (hb : d252967 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243651, d252967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243651, d252967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243652 q = 1) (hb : d252968 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243652, d252968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243652, d252968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243653 q = 1) (hb : d252969 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243653, d252969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243653, d252969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d243654 q = 1) (hb : d252970 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243654, d252970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243654, d252970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243655 q = 1) (hb : d252971 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243655, d252971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243655, d252971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro63513 (p : Pattern) (ha : d243661 p = 1) (hb : d252977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243656 q = 1) (hb : d252972 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243656, d252972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63512 q ha hb
    | true =>
      simp only [d243656, d252972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243657 q = 1) (hb : d252973 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243657, d252973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243657, d252973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243658 q = 1) (hb : d252974 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243658, d252974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243658, d252974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243659 q = 1) (hb : d252975 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243659, d252975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243659, d252975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243660 q = 1) (hb : d252976 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243660, d252976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243660, d252976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243661 q = 1) (hb : d252977 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243661, d252977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243661, d252977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63514 (p : Pattern) (ha : d243667 p = 1) (hb : d252983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243631 q = 1) (hb : d252957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243631, d252957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63507 q ha hb
    | true =>
      simp only [d243631, d252957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63509 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d252958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d252958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243637, d252958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d243662 q = 1) (hb : d252978 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243662, d252978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63513 q ha hb
    | true =>
      simp only [d243662, d252978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243663 q = 1) (hb : d252979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243663, d252979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243663, d252979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243664 q = 1) (hb : d252980 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d252980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d252980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243665 q = 1) (hb : d252981 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d252981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d252981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243666 q = 1) (hb : d252982 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d252982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d252982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243667 q = 1) (hb : d252983 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d252983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d252983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro63515 (p : Pattern) (ha : d243635 p = 1) (hb : d252988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243625 q = 1) (hb : d252951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243625, d252951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63508 q ha hb
    | true =>
      simp only [d243625, d252951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243626 q = 1) (hb : d252952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243626, d252952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243626, d252952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243632 q = 1) (hb : d252985 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243632, d252985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243632, d252985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243633 q = 1) (hb : d252986 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243633, d252986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243633, d252986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243634 q = 1) (hb : d252987 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243634, d252987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243634, d252987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243635 q = 1) (hb : d252988 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243635, d252988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243635, d252988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63516 (p : Pattern) (ha : d243674 p = 1) (hb : d252994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243669 q = 1) (hb : d252989 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243669, d252989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63515 q ha hb
    | true =>
      simp only [d243669, d252989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243670 q = 1) (hb : d252990 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243670, d252990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243670, d252990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243671 q = 1) (hb : d252991 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243671, d252991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243671, d252991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243672 q = 1) (hb : d252992 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243672, d252992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243672, d252992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243673 q = 1) (hb : d252993 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243673, d252993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243673, d252993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243674 q = 1) (hb : d252994 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243674, d252994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243674, d252994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63517 (p : Pattern) (ha : d243680 p = 1) (hb : d253000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243429 q = 1) (hb : d252791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243429, d252791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243429, d252791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63470 q ha hb
  have h2 (q : Pattern) (ha : d243430 q = 1) (hb : d252792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243430, d252792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243430, d252792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243439 q = 1) (hb : d252801 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243439, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63470 q ha hb
    | true =>
      simp only [d243439, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63473 q ha hb
  have h4 (q : Pattern) (ha : d243440 q = 1) (hb : d252802 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243440, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243440, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243441 q = 1) (hb : d252803 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243441, d252803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243441, d252803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243538 q = 1) (hb : d252883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243538, d252883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63488 q ha hb
    | true =>
      simp only [d243538, d252883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63495 q ha hb
  have h7 (q : Pattern) (ha : d243551 q = 1) (hb : d252896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243551, d252896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63496 q ha hb
    | true =>
      simp only [d243551, d252896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63497 q ha hb
  have h8 (q : Pattern) (ha : d243552 q = 1) (hb : d252897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243552, d252897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243552, d252897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243553 q = 1) (hb : d252898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d252898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243553, d252898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d243554 q = 1) (hb : d252899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d252899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243554, d252899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243558 q = 1) (hb : d252903 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d252903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243558, d252903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63498 q ha hb
  have h12 (q : Pattern) (ha : d243560 q = 1) (hb : d252905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243560, d252905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243560, d252905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63499 q ha hb
  have h13 (q : Pattern) (ha : d243561 q = 1) (hb : d252906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d252906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243561, d252906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243562 q = 1) (hb : d252907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d252907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243562, d252907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243563 q = 1) (hb : d252908 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d252908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243563, d252908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243564 q = 1) (hb : d252909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d252909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243564, d252909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243668 q = 1) (hb : d252984 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d252984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243668, d252984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63514 q ha hb
  have h18 (q : Pattern) (ha : d243675 q = 1) (hb : d252995 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243675, d252995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243675, d252995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63516 q ha hb
  have h19 (q : Pattern) (ha : d243676 q = 1) (hb : d252996 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d252996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243676, d252996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d243677 q = 1) (hb : d252997 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d252997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243677, d252997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243678 q = 1) (hb : d252998 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d252998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d243678, d252998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d243679 q = 1) (hb : d252999 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d252999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d243679, d252999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d243680 q = 1) (hb : d253000 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d253000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243680, d253000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro63518 (p : Pattern) (ha : d243686 p = 1) (hb : d253006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d253001 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d253001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d253001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63517 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d253002 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d253002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d253002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d253003 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d253003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d253003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d253004 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d253004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d253004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d253005 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d253005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d253005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d253006 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d253006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d253006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63519 (p : Pattern) (ha : d243692 p = 1) (hb : d253012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d251852 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d251852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63233 q ha hb
    | true =>
      simp only [d242306, d251852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63279 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d252122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d252122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d252122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63332 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d252123 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d252123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d252123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d252439 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d252439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d252439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63394 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d252440 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d252440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d252440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d252441 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d252441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d252441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d252741 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d252741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d252741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63458 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d252742 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d252742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d252742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d252743 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d252743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d252743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d252744 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d252744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d252744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d253007 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d253007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d253007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63518 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d253008 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d253008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d253008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d253009 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d253009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d253009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d253010 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d253010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d253010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d253011 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d253011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d253011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d253012 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d253012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d253012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro63520 (p : Pattern) (ha : d243698 p = 1) (hb : d253018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d253013 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d253013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63519 q ha hb
    | true =>
      simp only [d243693, d253013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d253014 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d253014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d253014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d253015 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d253015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d253015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d253016 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d253016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d253016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d253017 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d253017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d253017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d253018 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d253018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d253018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63521 (p : Pattern) (ha : d243704 p = 1) (hb : d253024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d253019 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d253019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63520 q ha hb
    | true =>
      simp only [d243699, d253019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d253020 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d253020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d253020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d253021 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d253021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d253021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d253022 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d253022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d253022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d253023 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d253023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d253023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d253024 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d253024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d253024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63522 (p : Pattern) (ha : d243710 p = 1) (hb : d253030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d253025 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d253025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63521 q ha hb
    | true =>
      simp only [d243705, d253025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d253026 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d253026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d253026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d253027 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d253027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d253027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d253028 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d253028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d253028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d253029 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d253029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d253029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d253030 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d253030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d253030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63523 (p : Pattern) (ha : d243716 p = 1) (hb : d253036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d253031 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d253031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63522 q ha hb
    | true =>
      simp only [d243711, d253031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d253032 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d253032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d253032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d253033 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d253033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d253033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d253034 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d253034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d253034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d253035 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d253035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d253035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d253036 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d253036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d253036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63524 (p : Pattern) (ha : d243722 p = 1) (hb : d253042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d253037 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d253037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63523 q ha hb
    | true =>
      simp only [d243717, d253037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d253038 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d253038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d253038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d253039 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d253039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d253039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d253040 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d253040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d253040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d253041 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d253041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d253041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d253042 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d253042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d253042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63525 (p : Pattern) (ha : d243728 p = 1) (hb : d253048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d253043 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d253043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63524 q ha hb
    | true =>
      simp only [d243723, d253043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d253044 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d253044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d253044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d253045 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d253045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d253045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d253046 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d253046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d253046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d253047 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d253047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d253047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d253048 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d253048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d253048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63526 (p : Pattern) (ha : d243734 p = 1) (hb : d253054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d253049 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d253049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63525 q ha hb
    | true =>
      simp only [d243729, d253049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d253050 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d253050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d253050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d253051 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d253051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d253051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d253052 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d253052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d253052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d253053 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d253053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d253053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d253054 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d253054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d253054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63527 (p : Pattern) (ha : d245682 p = 1) (hb : d251389 p = 1) : d253057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d251389 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d251389 q = 1) : d251418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62876 q ha hb
    | true =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d251389 q = 1) : d251478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25191 q = 1) (hb : d251389 q = 1) : d251479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25192 q = 1) (hb : d251389 q = 1) : d251480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25193 q = 1) (hb : d251389 q = 1) : d251481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245682 q = 1) (hb : d251389 q = 1) : d253057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245682, d253057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245682, d253057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro63528 (p : Pattern) (ha : d245692 p = 1) (hb : d251389 p = 1) : d253067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d251389 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d251389 q = 1) : d251454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62881 q ha hb
    | true =>
      simp only [d25166, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245688 q = 1) (hb : d251389 q = 1) : d253063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245688, d253063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245688, d253063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245689 q = 1) (hb : d251389 q = 1) : d253064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245689, d253064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245689, d253064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245690 q = 1) (hb : d251389 q = 1) : d253065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245690, d253065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245690, d253065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245691 q = 1) (hb : d251389 q = 1) : d253066 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245691, d253066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245691, d253066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245692 q = 1) (hb : d251389 q = 1) : d253067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245692, d253067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245692, d253067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro63529 (p : Pattern) (ha : d245698 p = 1) (hb : d251389 p = 1) : d253073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d251389 q = 1) : d251483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62884 q ha hb
    | true =>
      simp only [d25195, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62885 q ha hb
  have h2 (q : Pattern) (ha : d25196 q = 1) (hb : d251389 q = 1) : d251484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245680 q = 1) (hb : d251389 q = 1) : d253055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245680, d253055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245680, d253055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245681 q = 1) (hb : d251389 q = 1) : d253056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245681, d253056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245681, d253056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245683 q = 1) (hb : d251389 q = 1) : d253058 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245683, d253058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245683, d253058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63527 q ha hb
  have h6 (q : Pattern) (ha : d245684 q = 1) (hb : d251389 q = 1) : d253059 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245684, d253059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245684, d253059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245685 q = 1) (hb : d251389 q = 1) : d253060 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245685, d253060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245685, d253060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245686 q = 1) (hb : d251389 q = 1) : d253061 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245686, d253061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245686, d253061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245687 q = 1) (hb : d251389 q = 1) : d253062 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245687, d253062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245687, d253062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245693 q = 1) (hb : d251389 q = 1) : d253068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245693, d253068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245693, d253068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63528 q ha hb
  have h11 (q : Pattern) (ha : d245694 q = 1) (hb : d251389 q = 1) : d253069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245694, d253069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245694, d253069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245695 q = 1) (hb : d251389 q = 1) : d253070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245695, d253070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245695, d253070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245696 q = 1) (hb : d251389 q = 1) : d253071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245696, d253071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245696, d253071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245697 q = 1) (hb : d251389 q = 1) : d253072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245697, d253072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245697, d253072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245698 q = 1) (hb : d251389 q = 1) : d253073 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245698, d253073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245698, d253073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63530 (p : Pattern) (ha : d245704 p = 1) (hb : d251389 p = 1) : d253079 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d251389 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245699 q = 1) (hb : d251389 q = 1) : d253074 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245699, d253074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245699, d253074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63529 q ha hb
  have h3 (q : Pattern) (ha : d245700 q = 1) (hb : d251389 q = 1) : d253075 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245700, d253075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245700, d253075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245701 q = 1) (hb : d251389 q = 1) : d253076 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245701, d253076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245701, d253076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245702 q = 1) (hb : d251389 q = 1) : d253077 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245702, d253077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245702, d253077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245703 q = 1) (hb : d251389 q = 1) : d253078 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245703, d253078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245703, d253078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245704 q = 1) (hb : d251389 q = 1) : d253079 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245704, d253079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245704, d253079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro63531 (p : Pattern) (ha : d245707 p = 1) (hb : d251389 p = 1) : d253082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25402 q = 1) (hb : d251389 q = 1) : d251647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62914 q ha hb
    | true =>
      simp only [d25402, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62915 q ha hb
  have h2 (q : Pattern) (ha : d25403 q = 1) (hb : d251389 q = 1) : d251648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25404 q = 1) (hb : d251389 q = 1) : d251649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25404, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25405 q = 1) (hb : d251389 q = 1) : d251650 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25406 q = 1) (hb : d251389 q = 1) : d251651 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245707 q = 1) (hb : d251389 q = 1) : d253082 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245707, d253082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245707, d253082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63532 (p : Pattern) (ha : d245718 p = 1) (hb : d251389 p = 1) : d253093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245713 q = 1) (hb : d251389 q = 1) : d253088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245713, d253088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62949 q ha hb
    | true =>
      simp only [d245713, d253088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62921 q ha hb
  have h2 (q : Pattern) (ha : d245714 q = 1) (hb : d251389 q = 1) : d253089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245714, d253089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245714, d253089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245715 q = 1) (hb : d251389 q = 1) : d253090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245715, d253090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245715, d253090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245716 q = 1) (hb : d251389 q = 1) : d253091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245716, d253091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245716, d253091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245717 q = 1) (hb : d251389 q = 1) : d253092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245717, d253092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245717, d253092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245718 q = 1) (hb : d251389 q = 1) : d253093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245718, d253093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245718, d253093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63533 (p : Pattern) (ha : d245724 p = 1) (hb : d251389 p = 1) : d253099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25408 q = 1) (hb : d251389 q = 1) : d251653 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62913 q ha hb
    | true =>
      simp only [d25408, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62916 q ha hb
  have h2 (q : Pattern) (ha : d25409 q = 1) (hb : d251389 q = 1) : d251654 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25409, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245705 q = 1) (hb : d251389 q = 1) : d253080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245705, d253080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245705, d253080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245706 q = 1) (hb : d251389 q = 1) : d253081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245706, d253081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245706, d253081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245708 q = 1) (hb : d251389 q = 1) : d253083 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245708, d253083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245708, d253083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63531 q ha hb
  have h6 (q : Pattern) (ha : d245709 q = 1) (hb : d251389 q = 1) : d253084 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245709, d253084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245709, d253084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245710 q = 1) (hb : d251389 q = 1) : d253085 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245710, d253085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245710, d253085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245711 q = 1) (hb : d251389 q = 1) : d253086 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245711, d253086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245711, d253086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245712 q = 1) (hb : d251389 q = 1) : d253087 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245712, d253087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245712, d253087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245719 q = 1) (hb : d251389 q = 1) : d253094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245719, d253094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245719, d253094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63532 q ha hb
  have h11 (q : Pattern) (ha : d245720 q = 1) (hb : d251389 q = 1) : d253095 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245720, d253095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245720, d253095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245721 q = 1) (hb : d251389 q = 1) : d253096 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245721, d253096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245721, d253096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245722 q = 1) (hb : d251389 q = 1) : d253097 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245722, d253097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245722, d253097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245723 q = 1) (hb : d251389 q = 1) : d253098 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245723, d253098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245723, d253098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245724 q = 1) (hb : d251389 q = 1) : d253099 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245724, d253099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245724, d253099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63534 (p : Pattern) (ha : d245730 p = 1) (hb : d251389 p = 1) : d253105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245725 q = 1) (hb : d251389 q = 1) : d253100 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245725, d253100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245725, d253100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63533 q ha hb
  have h2 (q : Pattern) (ha : d245726 q = 1) (hb : d251389 q = 1) : d253101 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245726, d253101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245726, d253101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245727 q = 1) (hb : d251389 q = 1) : d253102 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245727, d253102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245727, d253102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245728 q = 1) (hb : d251389 q = 1) : d253103 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245728, d253103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245728, d253103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245729 q = 1) (hb : d251389 q = 1) : d253104 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245729, d253104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245729, d253104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245730 q = 1) (hb : d251389 q = 1) : d253105 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245730, d253105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245730, d253105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63535 (p : Pattern) (ha : d245734 p = 1) (hb : d251389 p = 1) : d253109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25735 q = 1) (hb : d251389 q = 1) : d251898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62963 q ha hb
    | true =>
      simp only [d25735, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62964 q ha hb
  have h2 (q : Pattern) (ha : d25736 q = 1) (hb : d251389 q = 1) : d251899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25737 q = 1) (hb : d251389 q = 1) : d251900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25737, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25738 q = 1) (hb : d251389 q = 1) : d251901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25739 q = 1) (hb : d251389 q = 1) : d251902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245734 q = 1) (hb : d251389 q = 1) : d253109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245734, d253109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245734, d253109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63536 (p : Pattern) (ha : d245745 p = 1) (hb : d251389 p = 1) : d253120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245740 q = 1) (hb : d251389 q = 1) : d253115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245740, d253115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63001 q ha hb
    | true =>
      simp only [d245740, d253115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62972 q ha hb
  have h2 (q : Pattern) (ha : d245741 q = 1) (hb : d251389 q = 1) : d253116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245741, d253116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245741, d253116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245742 q = 1) (hb : d251389 q = 1) : d253117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245742, d253117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245742, d253117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245743 q = 1) (hb : d251389 q = 1) : d253118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245743, d253118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245743, d253118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245744 q = 1) (hb : d251389 q = 1) : d253119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245744, d253119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245744, d253119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245745 q = 1) (hb : d251389 q = 1) : d253120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245745, d253120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245745, d253120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63537 (p : Pattern) (ha : d245751 p = 1) (hb : d251389 p = 1) : d253126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25741 q = 1) (hb : d251389 q = 1) : d251904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d251904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62962 q ha hb
    | true =>
      simp only [d25741, d251904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62965 q ha hb
  have h2 (q : Pattern) (ha : d25742 q = 1) (hb : d251389 q = 1) : d251905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d251905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25742, d251905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245732 q = 1) (hb : d251389 q = 1) : d253107 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245732, d253107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245732, d253107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245733 q = 1) (hb : d251389 q = 1) : d253108 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245733, d253108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245733, d253108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245735 q = 1) (hb : d251389 q = 1) : d253110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245735, d253110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245735, d253110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63535 q ha hb
  have h6 (q : Pattern) (ha : d245736 q = 1) (hb : d251389 q = 1) : d253111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245736, d253111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245736, d253111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245737 q = 1) (hb : d251389 q = 1) : d253112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245737, d253112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245737, d253112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245738 q = 1) (hb : d251389 q = 1) : d253113 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245738, d253113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245738, d253113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245739 q = 1) (hb : d251389 q = 1) : d253114 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245739, d253114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245739, d253114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245746 q = 1) (hb : d251389 q = 1) : d253121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245746, d253121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245746, d253121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63536 q ha hb
  have h11 (q : Pattern) (ha : d245747 q = 1) (hb : d251389 q = 1) : d253122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245747, d253122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245747, d253122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245748 q = 1) (hb : d251389 q = 1) : d253123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245748, d253123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245748, d253123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245749 q = 1) (hb : d251389 q = 1) : d253124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245749, d253124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245749, d253124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245750 q = 1) (hb : d251389 q = 1) : d253125 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245750, d253125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245750, d253125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245751 q = 1) (hb : d251389 q = 1) : d253126 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245751, d253126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245751, d253126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63538 (p : Pattern) (ha : d245757 p = 1) (hb : d251389 p = 1) : d253132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245752 q = 1) (hb : d251389 q = 1) : d253127 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245752, d253127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245752, d253127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63537 q ha hb
  have h2 (q : Pattern) (ha : d245753 q = 1) (hb : d251389 q = 1) : d253128 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245753, d253128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245753, d253128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245754 q = 1) (hb : d251389 q = 1) : d253129 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245754, d253129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245754, d253129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245755 q = 1) (hb : d251389 q = 1) : d253130 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245755, d253130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245755, d253130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245756 q = 1) (hb : d251389 q = 1) : d253131 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245756, d253131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245756, d253131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245757 q = 1) (hb : d251389 q = 1) : d253132 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245757, d253132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245757, d253132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63539 (p : Pattern) (ha : d245762 p = 1) (hb : d251389 p = 1) : d253137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26159 q = 1) (hb : d251389 q = 1) : d252190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d252190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63019 q ha hb
    | true =>
      simp only [d26159, d252190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63020 q ha hb
  have h2 (q : Pattern) (ha : d26160 q = 1) (hb : d251389 q = 1) : d252191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26161 q = 1) (hb : d251389 q = 1) : d252192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26161, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26162 q = 1) (hb : d251389 q = 1) : d252193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26163 q = 1) (hb : d251389 q = 1) : d252194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245762 q = 1) (hb : d251389 q = 1) : d253137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245762, d253137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245762, d253137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63540 (p : Pattern) (ha : d245773 p = 1) (hb : d251389 p = 1) : d253148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245768 q = 1) (hb : d251389 q = 1) : d253143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245768, d253143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63059 q ha hb
    | true =>
      simp only [d245768, d253143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63028 q ha hb
  have h2 (q : Pattern) (ha : d245769 q = 1) (hb : d251389 q = 1) : d253144 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245769, d253144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245769, d253144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245770 q = 1) (hb : d251389 q = 1) : d253145 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245770, d253145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245770, d253145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245771 q = 1) (hb : d251389 q = 1) : d253146 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245771, d253146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245771, d253146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245772 q = 1) (hb : d251389 q = 1) : d253147 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245772, d253147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245772, d253147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245773 q = 1) (hb : d251389 q = 1) : d253148 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245773, d253148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245773, d253148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63541 (p : Pattern) (ha : d245779 p = 1) (hb : d251389 p = 1) : d253154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26165 q = 1) (hb : d251389 q = 1) : d252196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d252196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63018 q ha hb
    | true =>
      simp only [d26165, d252196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63021 q ha hb
  have h2 (q : Pattern) (ha : d26166 q = 1) (hb : d251389 q = 1) : d252197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d252197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26166, d252197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245760 q = 1) (hb : d251389 q = 1) : d253135 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245760, d253135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245760, d253135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245761 q = 1) (hb : d251389 q = 1) : d253136 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245761, d253136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245761, d253136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245763 q = 1) (hb : d251389 q = 1) : d253138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245763, d253138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245763, d253138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63539 q ha hb
  have h6 (q : Pattern) (ha : d245764 q = 1) (hb : d251389 q = 1) : d253139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245764, d253139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245764, d253139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245765 q = 1) (hb : d251389 q = 1) : d253140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245765, d253140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245765, d253140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245766 q = 1) (hb : d251389 q = 1) : d253141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245766, d253141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245766, d253141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245767 q = 1) (hb : d251389 q = 1) : d253142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245767, d253142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245767, d253142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245774 q = 1) (hb : d251389 q = 1) : d253149 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245774, d253149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245774, d253149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63540 q ha hb
  have h11 (q : Pattern) (ha : d245775 q = 1) (hb : d251389 q = 1) : d253150 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245775, d253150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245775, d253150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245776 q = 1) (hb : d251389 q = 1) : d253151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245776, d253151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245776, d253151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245777 q = 1) (hb : d251389 q = 1) : d253152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245777, d253152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245777, d253152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245778 q = 1) (hb : d251389 q = 1) : d253153 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245778, d253153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245778, d253153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245779 q = 1) (hb : d251389 q = 1) : d253154 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245779, d253154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245779, d253154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63542 (p : Pattern) (ha : d245785 p = 1) (hb : d251389 p = 1) : d253160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245780 q = 1) (hb : d251389 q = 1) : d253155 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245780, d253155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245780, d253155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63541 q ha hb
  have h2 (q : Pattern) (ha : d245781 q = 1) (hb : d251389 q = 1) : d253156 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245781, d253156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245781, d253156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245782 q = 1) (hb : d251389 q = 1) : d253157 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245782, d253157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245782, d253157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245783 q = 1) (hb : d251389 q = 1) : d253158 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245783, d253158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245783, d253158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245784 q = 1) (hb : d251389 q = 1) : d253159 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245784, d253159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245784, d253159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245785 q = 1) (hb : d251389 q = 1) : d253160 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245785, d253160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245785, d253160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63543 (p : Pattern) (ha : d245791 p = 1) (hb : d251389 p = 1) : d253166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26626 q = 1) (hb : d251389 q = 1) : d252508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d252508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63079 q ha hb
    | true =>
      simp only [d26626, d252508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63080 q ha hb
  have h2 (q : Pattern) (ha : d26627 q = 1) (hb : d251389 q = 1) : d252509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26628 q = 1) (hb : d251389 q = 1) : d252510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26628, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26629 q = 1) (hb : d251389 q = 1) : d252511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26630 q = 1) (hb : d251389 q = 1) : d252512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245791 q = 1) (hb : d251389 q = 1) : d253166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245791, d253166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245791, d253166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63544 (p : Pattern) (ha : d245802 p = 1) (hb : d251389 p = 1) : d253177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245797 q = 1) (hb : d251389 q = 1) : d253172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245797, d253172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63120 q ha hb
    | true =>
      simp only [d245797, d253172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63088 q ha hb
  have h2 (q : Pattern) (ha : d245798 q = 1) (hb : d251389 q = 1) : d253173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245798, d253173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245798, d253173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245799 q = 1) (hb : d251389 q = 1) : d253174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245799, d253174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245799, d253174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245800 q = 1) (hb : d251389 q = 1) : d253175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245800, d253175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245800, d253175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245801 q = 1) (hb : d251389 q = 1) : d253176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245801, d253176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245801, d253176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245802 q = 1) (hb : d251389 q = 1) : d253177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245802, d253177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245802, d253177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63545 (p : Pattern) (ha : d245808 p = 1) (hb : d251389 p = 1) : d253183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26632 q = 1) (hb : d251389 q = 1) : d252514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d252514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63078 q ha hb
    | true =>
      simp only [d26632, d252514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63081 q ha hb
  have h2 (q : Pattern) (ha : d26633 q = 1) (hb : d251389 q = 1) : d252515 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d252515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26633, d252515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245789 q = 1) (hb : d251389 q = 1) : d253164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245789, d253164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245789, d253164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245790 q = 1) (hb : d251389 q = 1) : d253165 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245790, d253165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245790, d253165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245792 q = 1) (hb : d251389 q = 1) : d253167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245792, d253167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245792, d253167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63543 q ha hb
  have h6 (q : Pattern) (ha : d245793 q = 1) (hb : d251389 q = 1) : d253168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245793, d253168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245793, d253168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245794 q = 1) (hb : d251389 q = 1) : d253169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245794, d253169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245794, d253169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245795 q = 1) (hb : d251389 q = 1) : d253170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245795, d253170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245795, d253170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245796 q = 1) (hb : d251389 q = 1) : d253171 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245796, d253171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245796, d253171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245803 q = 1) (hb : d251389 q = 1) : d253178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245803, d253178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245803, d253178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63544 q ha hb
  have h11 (q : Pattern) (ha : d245804 q = 1) (hb : d251389 q = 1) : d253179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245804, d253179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245804, d253179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245805 q = 1) (hb : d251389 q = 1) : d253180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245805, d253180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245805, d253180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245806 q = 1) (hb : d251389 q = 1) : d253181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245806, d253181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245806, d253181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245807 q = 1) (hb : d251389 q = 1) : d253182 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245807, d253182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245807, d253182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245808 q = 1) (hb : d251389 q = 1) : d253183 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245808, d253183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245808, d253183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63546 (p : Pattern) (ha : d245814 p = 1) (hb : d251389 p = 1) : d253189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245809 q = 1) (hb : d251389 q = 1) : d253184 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245809, d253184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245809, d253184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63545 q ha hb
  have h2 (q : Pattern) (ha : d245810 q = 1) (hb : d251389 q = 1) : d253185 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245810, d253185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245810, d253185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245811 q = 1) (hb : d251389 q = 1) : d253186 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245811, d253186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245811, d253186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245812 q = 1) (hb : d251389 q = 1) : d253187 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245812, d253187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245812, d253187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245813 q = 1) (hb : d251389 q = 1) : d253188 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245813, d253188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245813, d253188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245814 q = 1) (hb : d251389 q = 1) : d253189 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245814, d253189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245814, d253189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63547 (p : Pattern) (ha : d245821 p = 1) (hb : d251389 p = 1) : d253196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27079 q = 1) (hb : d251389 q = 1) : d252795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d252795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63140 q ha hb
    | true =>
      simp only [d27079, d252795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63141 q ha hb
  have h2 (q : Pattern) (ha : d27080 q = 1) (hb : d251389 q = 1) : d252796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27081 q = 1) (hb : d251389 q = 1) : d252797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27081, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27082 q = 1) (hb : d251389 q = 1) : d252798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27083 q = 1) (hb : d251389 q = 1) : d252799 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245821 q = 1) (hb : d251389 q = 1) : d253196 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245821, d253196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245821, d253196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63548 (p : Pattern) (ha : d245832 p = 1) (hb : d251389 p = 1) : d253207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245827 q = 1) (hb : d251389 q = 1) : d253202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245827, d253202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63180 q ha hb
    | true =>
      simp only [d245827, d253202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63149 q ha hb
  have h2 (q : Pattern) (ha : d245828 q = 1) (hb : d251389 q = 1) : d253203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245828, d253203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245828, d253203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245829 q = 1) (hb : d251389 q = 1) : d253204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245829, d253204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245829, d253204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245830 q = 1) (hb : d251389 q = 1) : d253205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245830, d253205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245830, d253205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245831 q = 1) (hb : d251389 q = 1) : d253206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245831, d253206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245831, d253206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245832 q = 1) (hb : d251389 q = 1) : d253207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245832, d253207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245832, d253207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63549 (p : Pattern) (ha : d245838 p = 1) (hb : d251389 p = 1) : d253213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27085 q = 1) (hb : d251389 q = 1) : d252801 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63139 q ha hb
    | true =>
      simp only [d27085, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63142 q ha hb
  have h2 (q : Pattern) (ha : d27086 q = 1) (hb : d251389 q = 1) : d252802 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27086, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245819 q = 1) (hb : d251389 q = 1) : d253194 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245819, d253194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245819, d253194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245820 q = 1) (hb : d251389 q = 1) : d253195 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245820, d253195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245820, d253195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245822 q = 1) (hb : d251389 q = 1) : d253197 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245822, d253197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245822, d253197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63547 q ha hb
  have h6 (q : Pattern) (ha : d245823 q = 1) (hb : d251389 q = 1) : d253198 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245823, d253198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245823, d253198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245824 q = 1) (hb : d251389 q = 1) : d253199 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245824, d253199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245824, d253199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245825 q = 1) (hb : d251389 q = 1) : d253200 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245825, d253200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245825, d253200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245826 q = 1) (hb : d251389 q = 1) : d253201 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245826, d253201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245826, d253201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245833 q = 1) (hb : d251389 q = 1) : d253208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245833, d253208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245833, d253208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63548 q ha hb
  have h11 (q : Pattern) (ha : d245834 q = 1) (hb : d251389 q = 1) : d253209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245834, d253209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245834, d253209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245835 q = 1) (hb : d251389 q = 1) : d253210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245835, d253210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245835, d253210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245836 q = 1) (hb : d251389 q = 1) : d253211 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245836, d253211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245836, d253211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245837 q = 1) (hb : d251389 q = 1) : d253212 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245837, d253212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245837, d253212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245838 q = 1) (hb : d251389 q = 1) : d253213 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245838, d253213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245838, d253213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63550 (p : Pattern) (ha : d245844 p = 1) (hb : d251389 p = 1) : d253219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245839 q = 1) (hb : d251389 q = 1) : d253214 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245839, d253214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245839, d253214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63549 q ha hb
  have h2 (q : Pattern) (ha : d245840 q = 1) (hb : d251389 q = 1) : d253215 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245840, d253215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245840, d253215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245841 q = 1) (hb : d251389 q = 1) : d253216 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245841, d253216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245841, d253216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245842 q = 1) (hb : d251389 q = 1) : d253217 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245842, d253217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245842, d253217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245843 q = 1) (hb : d251389 q = 1) : d253218 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245843, d253218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245843, d253218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245844 q = 1) (hb : d251389 q = 1) : d253219 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245844, d253219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245844, d253219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63551 (p : Pattern) (ha : d245850 p = 1) (hb : d251389 p = 1) : d253225 p = 1 := by
  have h0 (q : Pattern) (ha : d245731 q = 1) (hb : d251389 q = 1) : d253106 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245731, d253106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63530 q ha hb
    | true =>
      simp only [d245731, d253106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63534 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245758 q = 1) (hb : d251389 q = 1) : d253133 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245758, d253133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245758, d253133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63538 q ha hb
  have h3 (q : Pattern) (ha : d245759 q = 1) (hb : d251389 q = 1) : d253134 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245759, d253134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245759, d253134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245786 q = 1) (hb : d251389 q = 1) : d253161 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245786, d253161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245786, d253161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63542 q ha hb
  have h5 (q : Pattern) (ha : d245787 q = 1) (hb : d251389 q = 1) : d253162 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245787, d253162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245787, d253162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245788 q = 1) (hb : d251389 q = 1) : d253163 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245788, d253163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245788, d253163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245815 q = 1) (hb : d251389 q = 1) : d253190 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245815, d253190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245815, d253190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63546 q ha hb
  have h8 (q : Pattern) (ha : d245816 q = 1) (hb : d251389 q = 1) : d253191 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245816, d253191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245816, d253191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245817 q = 1) (hb : d251389 q = 1) : d253192 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245817, d253192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245817, d253192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245818 q = 1) (hb : d251389 q = 1) : d253193 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245818, d253193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245818, d253193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245845 q = 1) (hb : d251389 q = 1) : d253220 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245845, d253220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245845, d253220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63550 q ha hb
  have h12 (q : Pattern) (ha : d245846 q = 1) (hb : d251389 q = 1) : d253221 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245846, d253221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245846, d253221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245847 q = 1) (hb : d251389 q = 1) : d253222 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245847, d253222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245847, d253222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245848 q = 1) (hb : d251389 q = 1) : d253223 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245848, d253223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245848, d253223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245849 q = 1) (hb : d251389 q = 1) : d253224 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245849, d253224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245849, d253224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245850 q = 1) (hb : d251389 q = 1) : d253225 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245850, d253225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245850, d253225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro63552 (p : Pattern) (ha : d245856 p = 1) (hb : d251389 p = 1) : d253231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245851 q = 1) (hb : d251389 q = 1) : d253226 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245851, d253226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63551 q ha hb
    | true =>
      simp only [d245851, d253226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245852 q = 1) (hb : d251389 q = 1) : d253227 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245852, d253227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245852, d253227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245853 q = 1) (hb : d251389 q = 1) : d253228 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245853, d253228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245853, d253228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245854 q = 1) (hb : d251389 q = 1) : d253229 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245854, d253229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245854, d253229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245855 q = 1) (hb : d251389 q = 1) : d253230 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245855, d253230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245855, d253230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245856 q = 1) (hb : d251389 q = 1) : d253231 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245856, d253231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245856, d253231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63553 (p : Pattern) (ha : d245862 p = 1) (hb : d251389 p = 1) : d253237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245857 q = 1) (hb : d251389 q = 1) : d253232 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245857, d253232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63552 q ha hb
    | true =>
      simp only [d245857, d253232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245858 q = 1) (hb : d251389 q = 1) : d253233 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245858, d253233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245858, d253233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245859 q = 1) (hb : d251389 q = 1) : d253234 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245859, d253234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245859, d253234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245860 q = 1) (hb : d251389 q = 1) : d253235 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245860, d253235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245860, d253235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245861 q = 1) (hb : d251389 q = 1) : d253236 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245861, d253236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245861, d253236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245862 q = 1) (hb : d251389 q = 1) : d253237 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245862, d253237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245862, d253237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63554 (p : Pattern) (ha : d245868 p = 1) (hb : d251389 p = 1) : d253243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245863 q = 1) (hb : d251389 q = 1) : d253238 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245863, d253238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63553 q ha hb
    | true =>
      simp only [d245863, d253238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245864 q = 1) (hb : d251389 q = 1) : d253239 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245864, d253239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245864, d253239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245865 q = 1) (hb : d251389 q = 1) : d253240 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245865, d253240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245865, d253240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245866 q = 1) (hb : d251389 q = 1) : d253241 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245866, d253241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245866, d253241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245867 q = 1) (hb : d251389 q = 1) : d253242 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245867, d253242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245867, d253242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245868 q = 1) (hb : d251389 q = 1) : d253243 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245868, d253243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245868, d253243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63555 (p : Pattern) (ha : d245874 p = 1) (hb : d251389 p = 1) : d253249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245869 q = 1) (hb : d251389 q = 1) : d253244 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245869, d253244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63554 q ha hb
    | true =>
      simp only [d245869, d253244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245870 q = 1) (hb : d251389 q = 1) : d253245 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245870, d253245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245870, d253245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245871 q = 1) (hb : d251389 q = 1) : d253246 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245871, d253246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245871, d253246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245872 q = 1) (hb : d251389 q = 1) : d253247 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245872, d253247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245872, d253247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245873 q = 1) (hb : d251389 q = 1) : d253248 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245873, d253248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245873, d253248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245874 q = 1) (hb : d251389 q = 1) : d253249 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245874, d253249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245874, d253249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63556 (p : Pattern) (ha : d245880 p = 1) (hb : d251389 p = 1) : d253255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245875 q = 1) (hb : d251389 q = 1) : d253250 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245875, d253250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63555 q ha hb
    | true =>
      simp only [d245875, d253250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245876 q = 1) (hb : d251389 q = 1) : d253251 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245876, d253251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245876, d253251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245877 q = 1) (hb : d251389 q = 1) : d253252 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245877, d253252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245877, d253252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245878 q = 1) (hb : d251389 q = 1) : d253253 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245878, d253253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245878, d253253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245879 q = 1) (hb : d251389 q = 1) : d253254 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245879, d253254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245879, d253254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245880 q = 1) (hb : d251389 q = 1) : d253255 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245880, d253255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245880, d253255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63557 (p : Pattern) (ha : d245886 p = 1) (hb : d251389 p = 1) : d253261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245881 q = 1) (hb : d251389 q = 1) : d253256 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245881, d253256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63556 q ha hb
    | true =>
      simp only [d245881, d253256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245882 q = 1) (hb : d251389 q = 1) : d253257 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245882, d253257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245882, d253257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245883 q = 1) (hb : d251389 q = 1) : d253258 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245883, d253258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245883, d253258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245884 q = 1) (hb : d251389 q = 1) : d253259 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245884, d253259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245884, d253259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245885 q = 1) (hb : d251389 q = 1) : d253260 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245885, d253260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245885, d253260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245886 q = 1) (hb : d251389 q = 1) : d253261 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245886, d253261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245886, d253261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63558 (p : Pattern) (ha : d245892 p = 1) (hb : d251389 p = 1) : d253267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245887 q = 1) (hb : d251389 q = 1) : d253262 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245887, d253262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63557 q ha hb
    | true =>
      simp only [d245887, d253262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245888 q = 1) (hb : d251389 q = 1) : d253263 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245888, d253263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245888, d253263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245889 q = 1) (hb : d251389 q = 1) : d253264 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245889, d253264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245889, d253264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245890 q = 1) (hb : d251389 q = 1) : d253265 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245890, d253265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245890, d253265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245891 q = 1) (hb : d251389 q = 1) : d253266 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245891, d253266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245891, d253266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245892 q = 1) (hb : d251389 q = 1) : d253267 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245892, d253267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245892, d253267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63559 (p : Pattern) (ha : d241986 p = 1) (hb : d251475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d241855 q = 1) (hb : d251411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63199 q ha hb
    | true =>
      simp only [d241855, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d241976 q = 1) (hb : d251471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d241976, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d241983 q = 1) (hb : d251472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241983, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d241984 q = 1) (hb : d251473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241984, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241985 q = 1) (hb : d251474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241985, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241986 q = 1) (hb : d251475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d241986, d251475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241986, d251475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63560 (p : Pattern) (ha : d242005 p = 1) (hb : d251482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d241855 q = 1) (hb : d251411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63199 q ha hb
    | true =>
      simp only [d241855, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d241976 q = 1) (hb : d251471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241976, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d241983 q = 1) (hb : d251472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241983, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d241984 q = 1) (hb : d251473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241984, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241985 q = 1) (hb : d251474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241985, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241991 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d241862 q = 1) (hb : d251418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63201 q ha hb
    | true =>
      simp only [d241862, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d241998 q = 1) (hb : d251478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d241998, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242002 q = 1) (hb : d251479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242002, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242003 q = 1) (hb : d251480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242003, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242003, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242004 q = 1) (hb : d251481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242004, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242004, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242005 q = 1) (hb : d251482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242005, d251482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242005, d251482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63561 (p : Pattern) (ha : d242014 p = 1) (hb : d253057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241862 q = 1) (hb : d251418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63201 q ha hb
    | true =>
      simp only [d241862, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d241998 q = 1) (hb : d251478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241998, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242002 q = 1) (hb : d251479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242002, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242012 q = 1) (hb : d251480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242012, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242012, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242013 q = 1) (hb : d251481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242013, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242013, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242014 q = 1) (hb : d253057 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242014, d253057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242014, d253057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63562 (p : Pattern) (ha : d242054 p = 1) (hb : d253067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241898 q = 1) (hb : d251454 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241898, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63206 q ha hb
    | true =>
      simp only [d241898, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d242044 q = 1) (hb : d253063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242044, d253063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242044, d253063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242051 q = 1) (hb : d253064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242051, d253064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242051, d253064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242052 q = 1) (hb : d253065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242052, d253065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242052, d253065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242053 q = 1) (hb : d253066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242053, d253066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242053, d253066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242054 q = 1) (hb : d253067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242054, d253067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242054, d253067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63563 (p : Pattern) (ha : d242060 p = 1) (hb : d253073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242006 q = 1) (hb : d251483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242006, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63559 q ha hb
    | true =>
      simp only [d242006, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63560 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242009 q = 1) (hb : d251484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242009, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242009, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242010 q = 1) (hb : d253055 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242010, d253055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242010, d253055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242011 q = 1) (hb : d253056 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242011, d253056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242011, d253056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242015 q = 1) (hb : d253058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242015, d253058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242015, d253058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63561 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242016 q = 1) (hb : d253059 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242016, d253059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242016, d253059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242017 q = 1) (hb : d253060 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242017, d253060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242017, d253060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242018 q = 1) (hb : d253061 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242018, d253061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242018, d253061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242019 q = 1) (hb : d253062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242019, d253062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242019, d253062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242055 q = 1) (hb : d253068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242055, d253068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242055, d253068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63562 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242056 q = 1) (hb : d253069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242056, d253069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242056, d253069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242057 q = 1) (hb : d253070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242057, d253070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242057, d253070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242058 q = 1) (hb : d253071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242058, d253071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242058, d253071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242059 q = 1) (hb : d253072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242059, d253072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242059, d253072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242060 q = 1) (hb : d253073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242060, d253073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242060, d253073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63564 (p : Pattern) (ha : d242066 p = 1) (hb : d253079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d241910 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61294 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d241911 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d241912 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d241913 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d241914 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242061 q = 1) (hb : d253074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242061, d253074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242061, d253074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63563 q ha hb
  have h8 (q : Pattern) (ha : d242062 q = 1) (hb : d253075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242062, d253075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242062, d253075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242063 q = 1) (hb : d253076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242063, d253076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242063, d253076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242064 q = 1) (hb : d253077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242064, d253077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242064, d253077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d242065 q = 1) (hb : d253078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242065, d253078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242065, d253078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d242066 q = 1) (hb : d253079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242066, d253079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d242066, d253079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro63565 (p : Pattern) (ha : d242177 p = 1) (hb : d251642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242084 q = 1) (hb : d251637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63236 q ha hb
    | true =>
      simp only [d242084, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63237 q ha hb
  have h5 (q : Pattern) (ha : d242167 q = 1) (hb : d251638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242167, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242174 q = 1) (hb : d251639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242174, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242175 q = 1) (hb : d251640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242175, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242176 q = 1) (hb : d251641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242176, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242177 q = 1) (hb : d251642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242177, d251642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242177, d251642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63566 (p : Pattern) (ha : d242198 p = 1) (hb : d251652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242084 q = 1) (hb : d251637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63236 q ha hb
    | true =>
      simp only [d242084, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63237 q ha hb
  have h4 (q : Pattern) (ha : d242167 q = 1) (hb : d251638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242167, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242174 q = 1) (hb : d251639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242174, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242175 q = 1) (hb : d251640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242175, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242176 q = 1) (hb : d251641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242176, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242094 q = 1) (hb : d251647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63239 q ha hb
    | true =>
      simp only [d242094, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63240 q ha hb
  have h13 (q : Pattern) (ha : d242191 q = 1) (hb : d251648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242191, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242195 q = 1) (hb : d251649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242195, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242196 q = 1) (hb : d251650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242196, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242196, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242197 q = 1) (hb : d251651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242197, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242197, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242198 q = 1) (hb : d251652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242198, d251652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242198, d251652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63567 (p : Pattern) (ha : d242218 p = 1) (hb : d253082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242094 q = 1) (hb : d251647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63239 q ha hb
    | true =>
      simp only [d242094, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63240 q ha hb
  have h3 (q : Pattern) (ha : d242191 q = 1) (hb : d251648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242191, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242195 q = 1) (hb : d251649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242195, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242216 q = 1) (hb : d251650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242216, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242216, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242217 q = 1) (hb : d251651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242217, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242217, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242218 q = 1) (hb : d253082 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242218, d253082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242218, d253082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63568 (p : Pattern) (ha : d242286 p = 1) (hb : d253093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242275 q = 1) (hb : d253088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242275, d253088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63273 q ha hb
    | true =>
      simp only [d242275, d253088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63276 q ha hb
  have h3 (q : Pattern) (ha : d242276 q = 1) (hb : d253089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242276, d253089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242276, d253089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242282 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242283 q = 1) (hb : d253090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242283, d253090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242283, d253090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242284 q = 1) (hb : d253091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242284, d253091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242284, d253091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242285 q = 1) (hb : d253092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242285, d253092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242285, d253092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242286 q = 1) (hb : d253093 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242286, d253093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242286, d253093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63569 (p : Pattern) (ha : d242299 p = 1) (hb : d253099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242199 q = 1) (hb : d251653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242199, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63565 q ha hb
    | true =>
      simp only [d242199, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63566 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242213 q = 1) (hb : d251654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242213, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242213, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242214 q = 1) (hb : d253080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242214, d253080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242214, d253080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242215 q = 1) (hb : d253081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242215, d253081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242215, d253081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242219 q = 1) (hb : d253083 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242219, d253083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242219, d253083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63567 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242221 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242222 q = 1) (hb : d253084 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242222, d253084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242222, d253084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242223 q = 1) (hb : d253085 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242223, d253085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242223, d253085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242224 q = 1) (hb : d253086 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242224, d253086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242224, d253086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242225 q = 1) (hb : d253087 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242225, d253087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242225, d253087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242287 q = 1) (hb : d253094 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242287, d253094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242287, d253094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63568 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242294 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242295 q = 1) (hb : d253095 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242295, d253095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242295, d253095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242296 q = 1) (hb : d253096 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242296, d253096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242296, d253096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242297 q = 1) (hb : d253097 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242297, d253097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242297, d253097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242298 q = 1) (hb : d253098 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242298, d253098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242298, d253098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242299 q = 1) (hb : d253099 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242299, d253099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242299, d253099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63570 (p : Pattern) (ha : d242305 p = 1) (hb : d253105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242300 q = 1) (hb : d253100 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242300, d253100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242300, d253100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63569 q ha hb
  have h2 (q : Pattern) (ha : d242301 q = 1) (hb : d253101 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242301, d253101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242301, d253101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242302 q = 1) (hb : d253102 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242302, d253102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242302, d253102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242303 q = 1) (hb : d253103 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242303, d253103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242303, d253103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242304 q = 1) (hb : d253104 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242304, d253104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242304, d253104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242305 q = 1) (hb : d253105 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242305, d253105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242305, d253105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63571 (p : Pattern) (ha : d242435 p = 1) (hb : d251893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242342 q = 1) (hb : d251888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63286 q ha hb
    | true =>
      simp only [d242342, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63287 q ha hb
  have h5 (q : Pattern) (ha : d242425 q = 1) (hb : d251889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242425, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242432 q = 1) (hb : d251890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242432, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242433 q = 1) (hb : d251891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242433, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242434 q = 1) (hb : d251892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242434, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242435 q = 1) (hb : d251893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242435, d251893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242435, d251893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63572 (p : Pattern) (ha : d242456 p = 1) (hb : d251903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242342 q = 1) (hb : d251888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63286 q ha hb
    | true =>
      simp only [d242342, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63287 q ha hb
  have h4 (q : Pattern) (ha : d242425 q = 1) (hb : d251889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242425, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242432 q = 1) (hb : d251890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242432, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242433 q = 1) (hb : d251891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242433, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242434 q = 1) (hb : d251892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242434, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242352 q = 1) (hb : d251898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63289 q ha hb
    | true =>
      simp only [d242352, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63290 q ha hb
  have h13 (q : Pattern) (ha : d242449 q = 1) (hb : d251899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242449, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242453 q = 1) (hb : d251900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242453, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242454 q = 1) (hb : d251901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242454, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242454, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242455 q = 1) (hb : d251902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242455, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242455, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242456 q = 1) (hb : d251903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242456, d251903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242456, d251903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63573 (p : Pattern) (ha : d242476 p = 1) (hb : d253109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242352 q = 1) (hb : d251898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63289 q ha hb
    | true =>
      simp only [d242352, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63290 q ha hb
  have h3 (q : Pattern) (ha : d242449 q = 1) (hb : d251899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242449, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242453 q = 1) (hb : d251900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242453, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242474 q = 1) (hb : d251901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242474, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242474, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242475 q = 1) (hb : d251902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242475, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242475, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242476 q = 1) (hb : d253109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242476, d253109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242476, d253109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63574 (p : Pattern) (ha : d242561 p = 1) (hb : d253120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242550 q = 1) (hb : d253115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242550, d253115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63326 q ha hb
    | true =>
      simp only [d242550, d253115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63329 q ha hb
  have h3 (q : Pattern) (ha : d242551 q = 1) (hb : d253116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242551, d253116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242551, d253116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242558 q = 1) (hb : d253117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242558, d253117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242558, d253117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242559 q = 1) (hb : d253118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242559, d253118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242559, d253118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242560 q = 1) (hb : d253119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242560, d253119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242560, d253119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242561 q = 1) (hb : d253120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242561, d253120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242561, d253120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63575 (p : Pattern) (ha : d242574 p = 1) (hb : d253126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242457 q = 1) (hb : d251904 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242457, d251904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63571 q ha hb
    | true =>
      simp only [d242457, d251904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242471 q = 1) (hb : d251905 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242471, d251905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242471, d251905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242472 q = 1) (hb : d253107 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242472, d253107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242472, d253107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242473 q = 1) (hb : d253108 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242473, d253108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242473, d253108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242477 q = 1) (hb : d253110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242477, d253110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242477, d253110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63573 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242479 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242480 q = 1) (hb : d253111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242480, d253111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242480, d253111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242481 q = 1) (hb : d253112 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242481, d253112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242481, d253112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242482 q = 1) (hb : d253113 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242482, d253113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242482, d253113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242483 q = 1) (hb : d253114 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242483, d253114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242483, d253114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242562 q = 1) (hb : d253121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242562, d253121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242562, d253121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63574 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242570 q = 1) (hb : d253122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242570, d253122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242570, d253122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242571 q = 1) (hb : d253123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242571, d253123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242571, d253123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242572 q = 1) (hb : d253124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242572, d253124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242572, d253124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242573 q = 1) (hb : d253125 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242573, d253125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242573, d253125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242574 q = 1) (hb : d253126 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242574, d253126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242574, d253126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63576 (p : Pattern) (ha : d242580 p = 1) (hb : d253132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242575 q = 1) (hb : d253127 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242575, d253127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242575, d253127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63575 q ha hb
  have h2 (q : Pattern) (ha : d242576 q = 1) (hb : d253128 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242576, d253128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242576, d253128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242577 q = 1) (hb : d253129 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242577, d253129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242577, d253129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242578 q = 1) (hb : d253130 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242578, d253130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242578, d253130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242579 q = 1) (hb : d253131 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242579, d253131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242579, d253131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242580 q = 1) (hb : d253132 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242580, d253132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242580, d253132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63577 (p : Pattern) (ha : d242768 p = 1) (hb : d252185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242662 q = 1) (hb : d252180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d252180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63344 q ha hb
    | true =>
      simp only [d242662, d252180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63345 q ha hb
  have h5 (q : Pattern) (ha : d242749 q = 1) (hb : d252181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242749, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242765 q = 1) (hb : d252182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242765, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242766 q = 1) (hb : d252183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242766, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242767 q = 1) (hb : d252184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242767, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242768 q = 1) (hb : d252185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242768, d252185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242768, d252185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63578 (p : Pattern) (ha : d242789 p = 1) (hb : d252195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242662 q = 1) (hb : d252180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d252180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63344 q ha hb
    | true =>
      simp only [d242662, d252180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63345 q ha hb
  have h4 (q : Pattern) (ha : d242749 q = 1) (hb : d252181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242749, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242765 q = 1) (hb : d252182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242765, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242766 q = 1) (hb : d252183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242766, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242767 q = 1) (hb : d252184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242767, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242672 q = 1) (hb : d252190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d252190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63347 q ha hb
    | true =>
      simp only [d242672, d252190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63348 q ha hb
  have h13 (q : Pattern) (ha : d242782 q = 1) (hb : d252191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242782, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242786 q = 1) (hb : d252192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242786, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242787 q = 1) (hb : d252193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242787, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242787, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242788 q = 1) (hb : d252194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242788, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242788, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242789 q = 1) (hb : d252195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242789, d252195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242789, d252195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63579 (p : Pattern) (ha : d242809 p = 1) (hb : d253137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242672 q = 1) (hb : d252190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d252190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63347 q ha hb
    | true =>
      simp only [d242672, d252190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63348 q ha hb
  have h3 (q : Pattern) (ha : d242782 q = 1) (hb : d252191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242782, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242786 q = 1) (hb : d252192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242786, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242807 q = 1) (hb : d252193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242807, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242807, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242808 q = 1) (hb : d252194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242808, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242808, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242809 q = 1) (hb : d253137 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242809, d253137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242809, d253137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63580 (p : Pattern) (ha : d242930 p = 1) (hb : d253148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242910 q = 1) (hb : d253143 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242910, d253143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63386 q ha hb
    | true =>
      simp only [d242910, d253143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63391 q ha hb
  have h3 (q : Pattern) (ha : d242911 q = 1) (hb : d253144 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242911, d253144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242911, d253144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242927 q = 1) (hb : d253145 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242927, d253145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242927, d253145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242928 q = 1) (hb : d253146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242928, d253146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242928, d253146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242929 q = 1) (hb : d253147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242929, d253147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242929, d253147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242930 q = 1) (hb : d253148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242930, d253148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242930, d253148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63581 (p : Pattern) (ha : d242943 p = 1) (hb : d253154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242790 q = 1) (hb : d252196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242790, d252196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63577 q ha hb
    | true =>
      simp only [d242790, d252196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63578 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242803 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242804 q = 1) (hb : d252197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242804, d252197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242804, d252197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242805 q = 1) (hb : d253135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242805, d253135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242805, d253135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242806 q = 1) (hb : d253136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242806, d253136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242806, d253136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242810 q = 1) (hb : d253138 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242810, d253138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242810, d253138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63579 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242812 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242813 q = 1) (hb : d253139 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242813, d253139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242813, d253139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242814 q = 1) (hb : d253140 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242814, d253140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242814, d253140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242815 q = 1) (hb : d253141 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242815, d253141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242815, d253141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242816 q = 1) (hb : d253142 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242816, d253142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242816, d253142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242931 q = 1) (hb : d253149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242931, d253149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242931, d253149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63580 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242938 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242939 q = 1) (hb : d253150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242939, d253150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242939, d253150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242940 q = 1) (hb : d253151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242940, d253151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242940, d253151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242941 q = 1) (hb : d253152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242941, d253152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242941, d253152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242942 q = 1) (hb : d253153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242942, d253153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242942, d253153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242943 q = 1) (hb : d253154 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242943, d253154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242943, d253154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63582 (p : Pattern) (ha : d242949 p = 1) (hb : d253160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242944 q = 1) (hb : d253155 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242944, d253155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242944, d253155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63581 q ha hb
  have h2 (q : Pattern) (ha : d242945 q = 1) (hb : d253156 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242945, d253156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242945, d253156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242946 q = 1) (hb : d253157 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242946, d253157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242946, d253157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242947 q = 1) (hb : d253158 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242947, d253158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242947, d253158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242948 q = 1) (hb : d253159 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242948, d253159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242948, d253159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242949 q = 1) (hb : d253160 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242949, d253160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242949, d253160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63583 (p : Pattern) (ha : d243151 p = 1) (hb : d252503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243045 q = 1) (hb : d252498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d252498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63406 q ha hb
    | true =>
      simp only [d243045, d252498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63407 q ha hb
  have h5 (q : Pattern) (ha : d243119 q = 1) (hb : d252499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243119, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243148 q = 1) (hb : d252500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243148, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243149 q = 1) (hb : d252501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243149, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243150 q = 1) (hb : d252502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243150, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243151 q = 1) (hb : d252503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243151, d252503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243151, d252503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63584 (p : Pattern) (ha : d243172 p = 1) (hb : d252513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243045 q = 1) (hb : d252498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d252498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63406 q ha hb
    | true =>
      simp only [d243045, d252498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63407 q ha hb
  have h4 (q : Pattern) (ha : d243119 q = 1) (hb : d252499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243119, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243148 q = 1) (hb : d252500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243148, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243149 q = 1) (hb : d252501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243149, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243150 q = 1) (hb : d252502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243150, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243157 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243162 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243055 q = 1) (hb : d252508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d252508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63409 q ha hb
    | true =>
      simp only [d243055, d252508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63410 q ha hb
  have h13 (q : Pattern) (ha : d243165 q = 1) (hb : d252509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243165, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243169 q = 1) (hb : d252510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243169, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243170 q = 1) (hb : d252511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243170, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243170, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243171 q = 1) (hb : d252512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243171, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243171, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243172 q = 1) (hb : d252513 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243172, d252513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243172, d252513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63585 (p : Pattern) (ha : d243192 p = 1) (hb : d253166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243055 q = 1) (hb : d252508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d252508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63409 q ha hb
    | true =>
      simp only [d243055, d252508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63410 q ha hb
  have h3 (q : Pattern) (ha : d243165 q = 1) (hb : d252509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243165, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243169 q = 1) (hb : d252510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243169, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243190 q = 1) (hb : d252511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243190, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243190, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243191 q = 1) (hb : d252512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243191, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243191, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243192 q = 1) (hb : d253166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243192, d253166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243192, d253166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63586 (p : Pattern) (ha : d243320 p = 1) (hb : d253177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243289 q = 1) (hb : d253172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243289, d253172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63449 q ha hb
    | true =>
      simp only [d243289, d253172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63455 q ha hb
  have h3 (q : Pattern) (ha : d243290 q = 1) (hb : d253173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243290, d253173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243290, d253173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243317 q = 1) (hb : d253174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243317, d253174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243317, d253174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243318 q = 1) (hb : d253175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243318, d253175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243318, d253175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243319 q = 1) (hb : d253176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243319, d253176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243319, d253176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243320 q = 1) (hb : d253177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243320, d253177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243320, d253177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63587 (p : Pattern) (ha : d243333 p = 1) (hb : d253183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243173 q = 1) (hb : d252514 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243173, d252514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63583 q ha hb
    | true =>
      simp only [d243173, d252514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63584 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243187 q = 1) (hb : d252515 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243187, d252515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243187, d252515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243188 q = 1) (hb : d253164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243188, d253164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243188, d253164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243189 q = 1) (hb : d253165 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243189, d253165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243189, d253165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243193 q = 1) (hb : d253167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243193, d253167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243193, d253167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63585 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243196 q = 1) (hb : d253168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243196, d253168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243196, d253168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243197 q = 1) (hb : d253169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243197, d253169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243197, d253169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243198 q = 1) (hb : d253170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243198, d253170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243198, d253170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243199 q = 1) (hb : d253171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243199, d253171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243199, d253171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243321 q = 1) (hb : d253178 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243321, d253178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243321, d253178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63586 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243329 q = 1) (hb : d253179 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243329, d253179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243329, d253179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243330 q = 1) (hb : d253180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243330, d253180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243330, d253180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243331 q = 1) (hb : d253181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243331, d253181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243331, d253181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243332 q = 1) (hb : d253182 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243332, d253182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243332, d253182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243333 q = 1) (hb : d253183 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243333, d253183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243333, d253183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63588 (p : Pattern) (ha : d243339 p = 1) (hb : d253189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243334 q = 1) (hb : d253184 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243334, d253184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243334, d253184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63587 q ha hb
  have h2 (q : Pattern) (ha : d243335 q = 1) (hb : d253185 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243335, d253185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243335, d253185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243336 q = 1) (hb : d253186 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243336, d253186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243336, d253186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243337 q = 1) (hb : d253187 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243337, d253187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243337, d253187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243338 q = 1) (hb : d253188 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243338, d253188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243338, d253188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243339 q = 1) (hb : d253189 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243339, d253189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243339, d253189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63589 (p : Pattern) (ha : d243516 p = 1) (hb : d252790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243423 q = 1) (hb : d252785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d252785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63468 q ha hb
    | true =>
      simp only [d243423, d252785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63469 q ha hb
  have h5 (q : Pattern) (ha : d243478 q = 1) (hb : d252786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243478, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243513 q = 1) (hb : d252787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243513, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243514 q = 1) (hb : d252788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243514, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243515 q = 1) (hb : d252789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243515, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243516 q = 1) (hb : d252790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243516, d252790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243516, d252790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63590 (p : Pattern) (ha : d243537 p = 1) (hb : d252800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243423 q = 1) (hb : d252785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d252785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63468 q ha hb
    | true =>
      simp only [d243423, d252785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63469 q ha hb
  have h4 (q : Pattern) (ha : d243478 q = 1) (hb : d252786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243478, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243513 q = 1) (hb : d252787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243513, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243514 q = 1) (hb : d252788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243514, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243515 q = 1) (hb : d252789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243515, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243522 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243527 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243433 q = 1) (hb : d252795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d252795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63471 q ha hb
    | true =>
      simp only [d243433, d252795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63472 q ha hb
  have h13 (q : Pattern) (ha : d243530 q = 1) (hb : d252796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243530, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243534 q = 1) (hb : d252797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243534, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243535 q = 1) (hb : d252798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243535, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243535, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243536 q = 1) (hb : d252799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243536, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243536, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243537 q = 1) (hb : d252800 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243537, d252800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243537, d252800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63591 (p : Pattern) (ha : d243557 p = 1) (hb : d253196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243433 q = 1) (hb : d252795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d252795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63471 q ha hb
    | true =>
      simp only [d243433, d252795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63472 q ha hb
  have h3 (q : Pattern) (ha : d243530 q = 1) (hb : d252796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243530, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243534 q = 1) (hb : d252797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243534, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243555 q = 1) (hb : d252798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243555, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243555, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243556 q = 1) (hb : d252799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243556, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243556, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243557 q = 1) (hb : d253196 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243557, d253196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243557, d253196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63592 (p : Pattern) (ha : d243667 p = 1) (hb : d253207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243636 q = 1) (hb : d253202 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243636, d253202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63509 q ha hb
    | true =>
      simp only [d243636, d253202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63515 q ha hb
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d253203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d253203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243637, d253203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243664 q = 1) (hb : d253204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d253204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d253204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243665 q = 1) (hb : d253205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d253205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d253205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243666 q = 1) (hb : d253206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d253206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d253206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243667 q = 1) (hb : d253207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d253207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d253207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63593 (p : Pattern) (ha : d243680 p = 1) (hb : d253213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243538 q = 1) (hb : d252801 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243538, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63589 q ha hb
    | true =>
      simp only [d243538, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63590 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243552 q = 1) (hb : d252802 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243552, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243552, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243553 q = 1) (hb : d253194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d253194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243553, d253194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243554 q = 1) (hb : d253195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d253195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243554, d253195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243558 q = 1) (hb : d253197 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d253197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243558, d253197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63591 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243560 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243561 q = 1) (hb : d253198 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d253198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243561, d253198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243562 q = 1) (hb : d253199 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d253199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243562, d253199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243563 q = 1) (hb : d253200 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d253200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243563, d253200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243564 q = 1) (hb : d253201 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d253201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243564, d253201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243668 q = 1) (hb : d253208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d253208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243668, d253208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63592 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243676 q = 1) (hb : d253209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d253209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243676, d253209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243677 q = 1) (hb : d253210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d253210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243677, d253210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243678 q = 1) (hb : d253211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d253211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243678, d253211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243679 q = 1) (hb : d253212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d253212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243679, d253212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243680 q = 1) (hb : d253213 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d253213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243680, d253213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63594 (p : Pattern) (ha : d243686 p = 1) (hb : d253219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d253214 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d253214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d253214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63593 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d253215 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d253215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d253215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d253216 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d253216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d253216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d253217 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d253217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d253217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d253218 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d253218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d253218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d253219 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d253219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d253219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63595 (p : Pattern) (ha : d243692 p = 1) (hb : d253225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d253106 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d253106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63564 q ha hb
    | true =>
      simp only [d242306, d253106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63570 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d253133 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d253133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d253133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63576 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d253134 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d253134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d253134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d253161 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d253161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d253161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63582 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d253162 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d253162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d253162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d253163 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d253163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d253163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d253190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d253190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d253190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63588 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d253191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d253191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d253191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d253192 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d253192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d253192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d253193 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d253193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d253193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d253220 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d253220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d253220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63594 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d253221 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d253221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d253221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d253222 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d253222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d253222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d253223 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d253223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d253223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d253224 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d253224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d253224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d253225 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d253225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d253225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro63596 (p : Pattern) (ha : d243698 p = 1) (hb : d253231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d253226 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d253226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63595 q ha hb
    | true =>
      simp only [d243693, d253226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d253227 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d253227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d253227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d253228 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d253228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d253228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d253229 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d253229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d253229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d253230 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d253230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d253230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d253231 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d253231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d253231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63597 (p : Pattern) (ha : d243704 p = 1) (hb : d253237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d253232 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d253232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63596 q ha hb
    | true =>
      simp only [d243699, d253232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d253233 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d253233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d253233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d253234 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d253234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d253234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d253235 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d253235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d253235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d253236 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d253236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d253236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d253237 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d253237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d253237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63598 (p : Pattern) (ha : d243710 p = 1) (hb : d253243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d253238 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d253238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63597 q ha hb
    | true =>
      simp only [d243705, d253238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d253239 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d253239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d253239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d253240 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d253240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d253240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d253241 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d253241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d253241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d253242 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d253242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d253242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d253243 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d253243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d253243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63599 (p : Pattern) (ha : d243716 p = 1) (hb : d253249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d253244 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d253244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63598 q ha hb
    | true =>
      simp only [d243711, d253244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d253245 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d253245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d253245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d253246 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d253246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d253246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d253247 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d253247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d253247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d253248 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d253248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d253248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d253249 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d253249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d253249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63600 (p : Pattern) (ha : d243722 p = 1) (hb : d253255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d253250 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d253250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63599 q ha hb
    | true =>
      simp only [d243717, d253250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d253251 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d253251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d253251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d253252 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d253252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d253252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d253253 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d253253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d253253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d253254 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d253254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d253254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d253255 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d253255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d253255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63601 (p : Pattern) (ha : d243728 p = 1) (hb : d253261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d253256 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d253256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63600 q ha hb
    | true =>
      simp only [d243723, d253256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d253257 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d253257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d253257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d253258 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d253258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d253258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d253259 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d253259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d253259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d253260 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d253260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d253260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d253261 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d253261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d253261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63602 (p : Pattern) (ha : d243734 p = 1) (hb : d253267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d253262 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d253262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63601 q ha hb
    | true =>
      simp only [d243729, d253262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d253263 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d253263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d253263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d253264 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d253264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d253264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d253265 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d253265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d253265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d253266 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d253266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d253266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d253267 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d253267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d253267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro63603 (p : Pattern) (ha : d245392 p = 1) (hb : d251475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d251411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245388 q = 1) (hb : d251471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245388, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245389 q = 1) (hb : d251472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245389, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245390 q = 1) (hb : d251473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245390, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245391 q = 1) (hb : d251474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245391, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245392 q = 1) (hb : d251475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245392, d251475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245392, d251475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63604 (p : Pattern) (ha : d245397 p = 1) (hb : d251482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d251411 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245388 q = 1) (hb : d251471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245388, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245389 q = 1) (hb : d251472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245389, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245390 q = 1) (hb : d251473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245390, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245391 q = 1) (hb : d251474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245391, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d251418 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245393 q = 1) (hb : d251478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245393, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245394 q = 1) (hb : d251479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245394, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245395 q = 1) (hb : d251480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245395, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245395, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245396 q = 1) (hb : d251481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245396, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245396, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245397 q = 1) (hb : d251482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245397, d251482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245397, d251482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63605 (p : Pattern) (ha : d245404 p = 1) (hb : d253057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d251418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245393 q = 1) (hb : d251478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245393, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245394 q = 1) (hb : d251479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245394, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245402 q = 1) (hb : d251480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245402, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245402, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245403 q = 1) (hb : d251481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245403, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245403, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245404 q = 1) (hb : d253057 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d253057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245404, d253057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63606 (p : Pattern) (ha : d245414 p = 1) (hb : d253067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30870 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d251454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245410 q = 1) (hb : d253063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d253063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245410, d253063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245411 q = 1) (hb : d253064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d253064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245411, d253064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245412 q = 1) (hb : d253065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d253065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245412, d253065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245413 q = 1) (hb : d253066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d253066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245413, d253066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245414 q = 1) (hb : d253067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d253067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245414, d253067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63607 (p : Pattern) (ha : d245420 p = 1) (hb : d253073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245398 q = 1) (hb : d251483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245398, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63603 q ha hb
    | true =>
      simp only [d245398, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63604 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245399 q = 1) (hb : d251484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245399, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245399, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245400 q = 1) (hb : d253055 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d253055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245400, d253055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245401 q = 1) (hb : d253056 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d253056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245401, d253056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245405 q = 1) (hb : d253058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d253058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245405, d253058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63605 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245406 q = 1) (hb : d253059 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d253059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245406, d253059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245407 q = 1) (hb : d253060 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d253060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245407, d253060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245408 q = 1) (hb : d253061 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d253061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245408, d253061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245409 q = 1) (hb : d253062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d253062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245409, d253062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245415 q = 1) (hb : d253068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d253068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245415, d253068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63606 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245416 q = 1) (hb : d253069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d253069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245416, d253069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245417 q = 1) (hb : d253070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d253070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245417, d253070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245418 q = 1) (hb : d253071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d253071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245418, d253071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245419 q = 1) (hb : d253072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d253072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245419, d253072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245420 q = 1) (hb : d253073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d253073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245420, d253073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63608 (p : Pattern) (ha : d245426 p = 1) (hb : d253079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d245383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61343 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d245384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d245385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d245386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d245387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245421 q = 1) (hb : d253074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d253074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245421, d253074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63607 q ha hb
  have h8 (q : Pattern) (ha : d245422 q = 1) (hb : d253075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d253075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245422, d253075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245423 q = 1) (hb : d253076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d253076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245423, d253076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245424 q = 1) (hb : d253077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d253077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245424, d253077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245425 q = 1) (hb : d253078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d253078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245425, d253078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245426 q = 1) (hb : d253079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d253079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d245426, d253079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro63609 (p : Pattern) (ha : d245431 p = 1) (hb : d251642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d251637 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245427 q = 1) (hb : d251638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245427, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245428 q = 1) (hb : d251639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245428, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245429 q = 1) (hb : d251640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245429, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245430 q = 1) (hb : d251641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245430, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245431 q = 1) (hb : d251642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245431, d251642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245431, d251642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63610 (p : Pattern) (ha : d245436 p = 1) (hb : d251652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d251637 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245427 q = 1) (hb : d251638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245427, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245428 q = 1) (hb : d251639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245428, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245429 q = 1) (hb : d251640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245429, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245430 q = 1) (hb : d251641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245430, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31072 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d251647 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245432 q = 1) (hb : d251648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245432, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245433 q = 1) (hb : d251649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245433, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245434 q = 1) (hb : d251650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245434, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245434, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245435 q = 1) (hb : d251651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245435, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245435, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245436 q = 1) (hb : d251652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245436, d251652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245436, d251652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63611 (p : Pattern) (ha : d245443 p = 1) (hb : d253082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d251647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245432 q = 1) (hb : d251648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245432, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245433 q = 1) (hb : d251649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245433, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245441 q = 1) (hb : d251650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245441, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245441, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245442 q = 1) (hb : d251651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245442, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245442, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245443 q = 1) (hb : d253082 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d253082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245443, d253082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63612 (p : Pattern) (ha : d245453 p = 1) (hb : d253093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253088 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245449 q = 1) (hb : d253089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d253089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245449, d253089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31202 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245450 q = 1) (hb : d253090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d253090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245450, d253090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245451 q = 1) (hb : d253091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d253091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245451, d253091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245452 q = 1) (hb : d253092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d253092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245452, d253092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245453 q = 1) (hb : d253093 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d253093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245453, d253093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63613 (p : Pattern) (ha : d245459 p = 1) (hb : d253099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245437 q = 1) (hb : d251653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245437, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63609 q ha hb
    | true =>
      simp only [d245437, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63610 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245438 q = 1) (hb : d251654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245438, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245438, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245439 q = 1) (hb : d253080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d253080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245439, d253080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245440 q = 1) (hb : d253081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d253081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245440, d253081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245444 q = 1) (hb : d253083 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d253083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245444, d253083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63611 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31113 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245445 q = 1) (hb : d253084 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d253084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245445, d253084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245446 q = 1) (hb : d253085 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d253085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245446, d253085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245447 q = 1) (hb : d253086 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d253086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245447, d253086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245448 q = 1) (hb : d253087 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d253087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245448, d253087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245454 q = 1) (hb : d253094 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d253094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245454, d253094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63612 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245455 q = 1) (hb : d253095 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d253095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245455, d253095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245456 q = 1) (hb : d253096 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d253096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245456, d253096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245457 q = 1) (hb : d253097 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d253097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245457, d253097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245458 q = 1) (hb : d253098 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d253098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245458, d253098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245459 q = 1) (hb : d253099 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d253099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245459, d253099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63614 (p : Pattern) (ha : d245465 p = 1) (hb : d253105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245460 q = 1) (hb : d253100 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d253100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245460, d253100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63613 q ha hb
  have h2 (q : Pattern) (ha : d245461 q = 1) (hb : d253101 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d253101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245461, d253101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245462 q = 1) (hb : d253102 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d253102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245462, d253102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245463 q = 1) (hb : d253103 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d253103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245463, d253103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245464 q = 1) (hb : d253104 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d253104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245464, d253104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245465 q = 1) (hb : d253105 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d253105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245465, d253105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63615 (p : Pattern) (ha : d245471 p = 1) (hb : d251893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d251888 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245467 q = 1) (hb : d251889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245467, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245468 q = 1) (hb : d251890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245468, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245469 q = 1) (hb : d251891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245469, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245470 q = 1) (hb : d251892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245470, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245471 q = 1) (hb : d251893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245471, d251893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245471, d251893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63616 (p : Pattern) (ha : d245476 p = 1) (hb : d251903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d251888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245467 q = 1) (hb : d251889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245467, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245468 q = 1) (hb : d251890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245468, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245469 q = 1) (hb : d251891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245469, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245470 q = 1) (hb : d251892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245470, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d251898 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245472 q = 1) (hb : d251899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245472, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245473 q = 1) (hb : d251900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245473, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245474 q = 1) (hb : d251901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245474, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245474, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245475 q = 1) (hb : d251902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245475, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245475, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245476 q = 1) (hb : d251903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245476, d251903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245476, d251903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63617 (p : Pattern) (ha : d245483 p = 1) (hb : d253109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d251898 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245472 q = 1) (hb : d251899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245472, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245473 q = 1) (hb : d251900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245473, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245481 q = 1) (hb : d251901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245481, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245481, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245482 q = 1) (hb : d251902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245482, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245482, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245483 q = 1) (hb : d253109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245483, d253109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245483, d253109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63618 (p : Pattern) (ha : d245493 p = 1) (hb : d253120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245489 q = 1) (hb : d253116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245489, d253116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245489, d253116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31591 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245490 q = 1) (hb : d253117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245490, d253117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245490, d253117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245491 q = 1) (hb : d253118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245491, d253118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245491, d253118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245492 q = 1) (hb : d253119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245492, d253119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245492, d253119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245493 q = 1) (hb : d253120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245493, d253120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245493, d253120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63619 (p : Pattern) (ha : d245499 p = 1) (hb : d253126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245477 q = 1) (hb : d251904 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245477, d251904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63615 q ha hb
    | true =>
      simp only [d245477, d251904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63616 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245478 q = 1) (hb : d251905 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245478, d251905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245478, d251905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245479 q = 1) (hb : d253107 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245479, d253107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245479, d253107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245480 q = 1) (hb : d253108 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245480, d253108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245480, d253108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245484 q = 1) (hb : d253110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245484, d253110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245484, d253110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63617 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31470 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245485 q = 1) (hb : d253111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245485, d253111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245485, d253111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245486 q = 1) (hb : d253112 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245486, d253112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245486, d253112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245487 q = 1) (hb : d253113 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245487, d253113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245487, d253113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245488 q = 1) (hb : d253114 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245488, d253114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245488, d253114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245494 q = 1) (hb : d253121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245494, d253121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245494, d253121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63618 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31607 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245495 q = 1) (hb : d253122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245495, d253122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245495, d253122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245496 q = 1) (hb : d253123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245496, d253123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245496, d253123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245497 q = 1) (hb : d253124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245497, d253124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245497, d253124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245498 q = 1) (hb : d253125 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245498, d253125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245498, d253125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245499 q = 1) (hb : d253126 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245499, d253126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245499, d253126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63620 (p : Pattern) (ha : d245505 p = 1) (hb : d253132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245500 q = 1) (hb : d253127 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245500, d253127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245500, d253127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63619 q ha hb
  have h2 (q : Pattern) (ha : d245501 q = 1) (hb : d253128 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245501, d253128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245501, d253128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245502 q = 1) (hb : d253129 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245502, d253129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245502, d253129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245503 q = 1) (hb : d253130 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245503, d253130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245503, d253130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245504 q = 1) (hb : d253131 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245504, d253131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245504, d253131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245505 q = 1) (hb : d253132 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245505, d253132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245505, d253132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63621 (p : Pattern) (ha : d245512 p = 1) (hb : d252185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d252180 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245508 q = 1) (hb : d252181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245508, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245509 q = 1) (hb : d252182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245509, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245510 q = 1) (hb : d252183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245510, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245511 q = 1) (hb : d252184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245511, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245512 q = 1) (hb : d252185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d252185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d252185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63622 (p : Pattern) (ha : d245517 p = 1) (hb : d252195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d252180 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245508 q = 1) (hb : d252181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245508, d252181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245509 q = 1) (hb : d252182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245509, d252182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245510 q = 1) (hb : d252183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245510, d252183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245511 q = 1) (hb : d252184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245511, d252184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d252190 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245513 q = 1) (hb : d252191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245513, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245514 q = 1) (hb : d252192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245514, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245515 q = 1) (hb : d252193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245515, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245516 q = 1) (hb : d252194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245516, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245517 q = 1) (hb : d252195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d252195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245517, d252195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63623 (p : Pattern) (ha : d245524 p = 1) (hb : d253137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d252190 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245513 q = 1) (hb : d252191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d252191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245514 q = 1) (hb : d252192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245514, d252192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245522 q = 1) (hb : d252193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245522, d252193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245523 q = 1) (hb : d252194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245523, d252194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245524 q = 1) (hb : d253137 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d253137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245524, d253137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63624 (p : Pattern) (ha : d245534 p = 1) (hb : d253148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253143 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245530 q = 1) (hb : d253144 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d253144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d253144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245531 q = 1) (hb : d253145 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d253145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245531, d253145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245532 q = 1) (hb : d253146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d253146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245532, d253146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245533 q = 1) (hb : d253147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d253147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245533, d253147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245534 q = 1) (hb : d253148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d253148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245534, d253148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63625 (p : Pattern) (ha : d245540 p = 1) (hb : d253154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245518 q = 1) (hb : d252196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d252196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63621 q ha hb
    | true =>
      simp only [d245518, d252196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245519 q = 1) (hb : d252197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d252197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245519, d252197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245520 q = 1) (hb : d253135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d253135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245520, d253135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245521 q = 1) (hb : d253136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d253136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245521, d253136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245525 q = 1) (hb : d253138 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d253138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245525, d253138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63623 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245526 q = 1) (hb : d253139 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d253139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245526, d253139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245527 q = 1) (hb : d253140 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d253140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245527, d253140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245528 q = 1) (hb : d253141 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d253141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245528, d253141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245529 q = 1) (hb : d253142 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d253142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245529, d253142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245535 q = 1) (hb : d253149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d253149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245535, d253149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63624 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245536 q = 1) (hb : d253150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d253150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245536, d253150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245537 q = 1) (hb : d253151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d253151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245537, d253151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245538 q = 1) (hb : d253152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d253152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245538, d253152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245539 q = 1) (hb : d253153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d253153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245539, d253153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245540 q = 1) (hb : d253154 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d253154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245540, d253154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63626 (p : Pattern) (ha : d245546 p = 1) (hb : d253160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245541 q = 1) (hb : d253155 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d253155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245541, d253155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63625 q ha hb
  have h2 (q : Pattern) (ha : d245542 q = 1) (hb : d253156 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d253156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245542, d253156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245543 q = 1) (hb : d253157 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d253157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245543, d253157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245544 q = 1) (hb : d253158 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d253158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245544, d253158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245545 q = 1) (hb : d253159 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d253159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245545, d253159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245546 q = 1) (hb : d253160 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d253160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245546, d253160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63627 (p : Pattern) (ha : d245554 p = 1) (hb : d252503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d252498 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245550 q = 1) (hb : d252499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245550, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245551 q = 1) (hb : d252500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245551, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245552 q = 1) (hb : d252501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245552, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245553 q = 1) (hb : d252502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245553, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245554 q = 1) (hb : d252503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245554, d252503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245554, d252503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63628 (p : Pattern) (ha : d245559 p = 1) (hb : d252513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d252498 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245550 q = 1) (hb : d252499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245550, d252499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245551 q = 1) (hb : d252500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245551, d252500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245552 q = 1) (hb : d252501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245552, d252501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245553 q = 1) (hb : d252502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245553, d252502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d252508 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245555 q = 1) (hb : d252509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245555, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245556 q = 1) (hb : d252510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245556, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245557 q = 1) (hb : d252511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245557, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245557, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245558 q = 1) (hb : d252512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245558, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245558, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245559 q = 1) (hb : d252513 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245559, d252513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245559, d252513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63629 (p : Pattern) (ha : d245566 p = 1) (hb : d253166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d252508 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245555 q = 1) (hb : d252509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245555, d252509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245556 q = 1) (hb : d252510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245556, d252510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245564 q = 1) (hb : d252511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245564, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245564, d252511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245565 q = 1) (hb : d252512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245565, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245565, d252512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245566 q = 1) (hb : d253166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245566, d253166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245566, d253166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63630 (p : Pattern) (ha : d245576 p = 1) (hb : d253177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253172 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245572 q = 1) (hb : d253173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245572, d253173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245572, d253173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245573 q = 1) (hb : d253174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245573, d253174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245573, d253174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245574 q = 1) (hb : d253175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245574, d253175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245574, d253175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245575 q = 1) (hb : d253176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245575, d253176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245575, d253176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245576 q = 1) (hb : d253177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245576, d253177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245576, d253177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63631 (p : Pattern) (ha : d245582 p = 1) (hb : d253183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245560 q = 1) (hb : d252514 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245560, d252514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63627 q ha hb
    | true =>
      simp only [d245560, d252514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63628 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245561 q = 1) (hb : d252515 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245561, d252515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245561, d252515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245562 q = 1) (hb : d253164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245562, d253164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245562, d253164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245563 q = 1) (hb : d253165 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245563, d253165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245563, d253165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245567 q = 1) (hb : d253167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245567, d253167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245567, d253167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63629 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245568 q = 1) (hb : d253168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245568, d253168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245568, d253168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245569 q = 1) (hb : d253169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245569, d253169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245569, d253169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245570 q = 1) (hb : d253170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245570, d253170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245570, d253170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245571 q = 1) (hb : d253171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245571, d253171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245571, d253171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245577 q = 1) (hb : d253178 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245577, d253178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245577, d253178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63630 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32671 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245578 q = 1) (hb : d253179 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245578, d253179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245578, d253179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245579 q = 1) (hb : d253180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245579, d253180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245579, d253180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245580 q = 1) (hb : d253181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245580, d253181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245580, d253181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245581 q = 1) (hb : d253182 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245581, d253182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245581, d253182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245582 q = 1) (hb : d253183 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245582, d253183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245582, d253183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63632 (p : Pattern) (ha : d245588 p = 1) (hb : d253189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245583 q = 1) (hb : d253184 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245583, d253184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245583, d253184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63631 q ha hb
  have h2 (q : Pattern) (ha : d245584 q = 1) (hb : d253185 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245584, d253185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245584, d253185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245585 q = 1) (hb : d253186 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245585, d253186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245585, d253186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245586 q = 1) (hb : d253187 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245586, d253187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245586, d253187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245587 q = 1) (hb : d253188 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245587, d253188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245587, d253188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245588 q = 1) (hb : d253189 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245588, d253189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245588, d253189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63633 (p : Pattern) (ha : d245597 p = 1) (hb : d252790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d252785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245593 q = 1) (hb : d252786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245593, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245594 q = 1) (hb : d252787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245594, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245595 q = 1) (hb : d252788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245595, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245596 q = 1) (hb : d252789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245596, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245597 q = 1) (hb : d252790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245597, d252790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245597, d252790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro63634 (p : Pattern) (ha : d245602 p = 1) (hb : d252800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d252785 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245593 q = 1) (hb : d252786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245593, d252786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245594 q = 1) (hb : d252787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245594, d252787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245595 q = 1) (hb : d252788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245595, d252788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245596 q = 1) (hb : d252789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245596, d252789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32950 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d252795 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245598 q = 1) (hb : d252796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245598, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245599 q = 1) (hb : d252797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245599, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245600 q = 1) (hb : d252798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245600, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245600, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245601 q = 1) (hb : d252799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245601, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245601, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245602 q = 1) (hb : d252800 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245602, d252800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245602, d252800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro63635 (p : Pattern) (ha : d245609 p = 1) (hb : d253196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d252795 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245598 q = 1) (hb : d252796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245598, d252796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245599 q = 1) (hb : d252797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245599, d252797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245607 q = 1) (hb : d252798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245607, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245607, d252798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245608 q = 1) (hb : d252799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245608, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245608, d252799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245609 q = 1) (hb : d253196 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245609, d253196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245609, d253196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63636 (p : Pattern) (ha : d245619 p = 1) (hb : d253207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245615 q = 1) (hb : d253203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245615, d253203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245615, d253203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245616 q = 1) (hb : d253204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245616, d253204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245616, d253204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245617 q = 1) (hb : d253205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245617, d253205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245617, d253205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245618 q = 1) (hb : d253206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245618, d253206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245618, d253206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245619 q = 1) (hb : d253207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245619, d253207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245619, d253207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63637 (p : Pattern) (ha : d245625 p = 1) (hb : d253213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245603 q = 1) (hb : d252801 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245603, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63633 q ha hb
    | true =>
      simp only [d245603, d252801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245604 q = 1) (hb : d252802 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245604, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245604, d252802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245605 q = 1) (hb : d253194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245605, d253194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245605, d253194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245606 q = 1) (hb : d253195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245606, d253195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245606, d253195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245610 q = 1) (hb : d253197 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245610, d253197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245610, d253197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63635 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245611 q = 1) (hb : d253198 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245611, d253198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245611, d253198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245612 q = 1) (hb : d253199 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245612, d253199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245612, d253199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245613 q = 1) (hb : d253200 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245613, d253200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245613, d253200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245614 q = 1) (hb : d253201 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245614, d253201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245614, d253201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245620 q = 1) (hb : d253208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245620, d253208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245620, d253208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63636 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245621 q = 1) (hb : d253209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245621, d253209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245621, d253209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245622 q = 1) (hb : d253210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245622, d253210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245622, d253210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245623 q = 1) (hb : d253211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245623, d253211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245623, d253211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245624 q = 1) (hb : d253212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245624, d253212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245624, d253212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245625 q = 1) (hb : d253213 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245625, d253213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245625, d253213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63638 (p : Pattern) (ha : d245631 p = 1) (hb : d253219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245626 q = 1) (hb : d253214 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245626, d253214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245626, d253214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63637 q ha hb
  have h2 (q : Pattern) (ha : d245627 q = 1) (hb : d253215 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245627, d253215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245627, d253215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245628 q = 1) (hb : d253216 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245628, d253216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245628, d253216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245629 q = 1) (hb : d253217 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245629, d253217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245629, d253217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245630 q = 1) (hb : d253218 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245630, d253218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245630, d253218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245631 q = 1) (hb : d253219 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245631, d253219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245631, d253219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63639 (p : Pattern) (ha : d245637 p = 1) (hb : d253225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d245466 q = 1) (hb : d253106 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245466, d253106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63608 q ha hb
    | true =>
      simp only [d245466, d253106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63614 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245506 q = 1) (hb : d253133 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245506, d253133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245506, d253133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63620 q ha hb
  have h3 (q : Pattern) (ha : d245507 q = 1) (hb : d253134 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245507, d253134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245507, d253134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245547 q = 1) (hb : d253161 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245547, d253161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245547, d253161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63626 q ha hb
  have h5 (q : Pattern) (ha : d245548 q = 1) (hb : d253162 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245548, d253162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245548, d253162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245549 q = 1) (hb : d253163 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245549, d253163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245549, d253163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245589 q = 1) (hb : d253190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245589, d253190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245589, d253190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63632 q ha hb
  have h8 (q : Pattern) (ha : d245590 q = 1) (hb : d253191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245590, d253191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245590, d253191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245591 q = 1) (hb : d253192 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245591, d253192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245591, d253192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245592 q = 1) (hb : d253193 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245592, d253193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245592, d253193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245632 q = 1) (hb : d253220 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245632, d253220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245632, d253220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63638 q ha hb
  have h12 (q : Pattern) (ha : d245633 q = 1) (hb : d253221 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245633, d253221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245633, d253221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245634 q = 1) (hb : d253222 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245634, d253222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245634, d253222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245635 q = 1) (hb : d253223 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245635, d253223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245635, d253223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245636 q = 1) (hb : d253224 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245636, d253224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245636, d253224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245637 q = 1) (hb : d253225 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245637, d253225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245637, d253225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro63640 (p : Pattern) (ha : d245643 p = 1) (hb : d253231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245638 q = 1) (hb : d253226 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245638, d253226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63639 q ha hb
    | true =>
      simp only [d245638, d253226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245639 q = 1) (hb : d253227 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245639, d253227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245639, d253227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245640 q = 1) (hb : d253228 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245640, d253228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245640, d253228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245641 q = 1) (hb : d253229 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245641, d253229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245641, d253229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245642 q = 1) (hb : d253230 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245642, d253230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245642, d253230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245643 q = 1) (hb : d253231 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245643, d253231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245643, d253231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63641 (p : Pattern) (ha : d245649 p = 1) (hb : d253237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245644 q = 1) (hb : d253232 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245644, d253232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63640 q ha hb
    | true =>
      simp only [d245644, d253232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245645 q = 1) (hb : d253233 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245645, d253233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245645, d253233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245646 q = 1) (hb : d253234 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245646, d253234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245646, d253234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245647 q = 1) (hb : d253235 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245647, d253235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245647, d253235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245648 q = 1) (hb : d253236 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245648, d253236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245648, d253236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245649 q = 1) (hb : d253237 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245649, d253237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245649, d253237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63642 (p : Pattern) (ha : d245655 p = 1) (hb : d253243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245650 q = 1) (hb : d253238 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245650, d253238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63641 q ha hb
    | true =>
      simp only [d245650, d253238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245651 q = 1) (hb : d253239 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245651, d253239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245651, d253239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245652 q = 1) (hb : d253240 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245652, d253240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245652, d253240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245653 q = 1) (hb : d253241 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245653, d253241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245653, d253241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245654 q = 1) (hb : d253242 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245654, d253242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245654, d253242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245655 q = 1) (hb : d253243 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245655, d253243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245655, d253243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63643 (p : Pattern) (ha : d245661 p = 1) (hb : d253249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245656 q = 1) (hb : d253244 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245656, d253244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63642 q ha hb
    | true =>
      simp only [d245656, d253244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245657 q = 1) (hb : d253245 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245657, d253245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245657, d253245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245658 q = 1) (hb : d253246 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245658, d253246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245658, d253246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245659 q = 1) (hb : d253247 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245659, d253247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245659, d253247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245660 q = 1) (hb : d253248 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245660, d253248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245660, d253248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245661 q = 1) (hb : d253249 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245661, d253249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245661, d253249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63644 (p : Pattern) (ha : d245667 p = 1) (hb : d253255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245662 q = 1) (hb : d253250 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245662, d253250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63643 q ha hb
    | true =>
      simp only [d245662, d253250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245663 q = 1) (hb : d253251 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245663, d253251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245663, d253251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245664 q = 1) (hb : d253252 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245664, d253252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245664, d253252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245665 q = 1) (hb : d253253 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245665, d253253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245665, d253253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245666 q = 1) (hb : d253254 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245666, d253254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245666, d253254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245667 q = 1) (hb : d253255 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245667, d253255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245667, d253255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63645 (p : Pattern) (ha : d245673 p = 1) (hb : d253261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245668 q = 1) (hb : d253256 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245668, d253256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63644 q ha hb
    | true =>
      simp only [d245668, d253256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245669 q = 1) (hb : d253257 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245669, d253257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245669, d253257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245670 q = 1) (hb : d253258 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245670, d253258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245670, d253258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245671 q = 1) (hb : d253259 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245671, d253259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245671, d253259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245672 q = 1) (hb : d253260 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245672, d253260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245672, d253260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245673 q = 1) (hb : d253261 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245673, d253261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245673, d253261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63646 (p : Pattern) (ha : d245679 p = 1) (hb : d253267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245674 q = 1) (hb : d253262 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245674, d253262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63645 q ha hb
    | true =>
      simp only [d245674, d253262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245675 q = 1) (hb : d253263 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245675, d253263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245675, d253263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245676 q = 1) (hb : d253264 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245676, d253264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245676, d253264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245677 q = 1) (hb : d253265 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245677, d253265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245677, d253265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245678 q = 1) (hb : d253266 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245678, d253266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245678, d253266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245679 q = 1) (hb : d253267 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245679, d253267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245679, d253267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63647 (p : Pattern) (ha : d18 p = 1) (hb : d253271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d18, d253271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18, d253271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro63648 (p : Pattern) (ha : d24 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63647 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d24 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro63649 (p : Pattern) (ha : d30 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63650 (p : Pattern) (ha : d36 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63651 (p : Pattern) (ha : d42 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63652 (p : Pattern) (ha : d48 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63653 (p : Pattern) (ha : d49 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63654 (p : Pattern) (ha : d55 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63655 (p : Pattern) (ha : d60 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63656 (p : Pattern) (ha : d71 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63657 (p : Pattern) (ha : d77 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63656 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63658 (p : Pattern) (ha : d83 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63657 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63659 (p : Pattern) (ha : d89 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63658 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63660 (p : Pattern) (ha : d95 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63652 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63654 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63655 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63659 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63661 (p : Pattern) (ha : d104 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63662 (p : Pattern) (ha : d111 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63663 (p : Pattern) (ha : d213 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63664 (p : Pattern) (ha : d116 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63665 (p : Pattern) (ha : d123 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63666 (p : Pattern) (ha : d132 p = 1) (hb : d253271 p = 1) : d38813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17 q = 1) (hb : d253269 q = 1) : d17 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132 q = 1) (hb : d253271 q = 1) : d38813 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d253271, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132, d253271, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro63667 (p : Pattern) (ha : d25104 p = 1) (hb : d253272 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d253271 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63666 q ha hb
    | true =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d253271 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9796 q = 1) (hb : d253272 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63647 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25102 q = 1) (hb : d253272 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25102, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25103 q = 1) (hb : d253272 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25103, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h12 (q : Pattern) (ha : d23 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h13 (q : Pattern) (ha : d25104 q = 1) (hb : d253272 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25104, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro63668 (p : Pattern) (ha : d25110 p = 1) (hb : d253272 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25105 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63667 q ha hb
    | true =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25106 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25107 q = 1) (hb : d253272 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25108 q = 1) (hb : d253272 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25108, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25109 q = 1) (hb : d253272 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25109, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25110 q = 1) (hb : d253272 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25110, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63669 (p : Pattern) (ha : d25116 p = 1) (hb : d253272 p = 1) : d257200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25111 q = 1) (hb : d253272 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
    | true =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
  have h2 (q : Pattern) (ha : d25112 q = 1) (hb : d253272 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25113 q = 1) (hb : d253272 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25114 q = 1) (hb : d253272 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25114, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25115 q = 1) (hb : d253272 q = 1) : d257199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25115, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25116 q = 1) (hb : d253272 q = 1) : d257200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25116, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro63670 (p : Pattern) (ha : d25122 p = 1) (hb : d253272 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25121 q = 1) (hb : d253272 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25121, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25122 q = 1) (hb : d253272 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25122, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63671 (p : Pattern) (ha : d201977 p = 1) (hb : d253272 p = 1) : d257212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63664 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63665 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25123 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
    | true =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
  have h9 (q : Pattern) (ha : d201973 q = 1) (hb : d253272 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201973, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d201974 q = 1) (hb : d253272 q = 1) : d257209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201974, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201975 q = 1) (hb : d253272 q = 1) : d257210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201975, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201976 q = 1) (hb : d253272 q = 1) : d257211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201976, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d201977 q = 1) (hb : d253272 q = 1) : d257212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201977, d257212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201977, d257212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63672 (p : Pattern) (ha : d194 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63673 (p : Pattern) (ha : d199 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63674 (p : Pattern) (ha : d25129 p = 1) (hb : d253272 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25121 q = 1) (hb : d253272 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25121, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25129 q = 1) (hb : d253272 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25129, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63675 (p : Pattern) (ha : d201982 p = 1) (hb : d253272 p = 1) : d257219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63664 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63665 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25123 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
    | true =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
  have h9 (q : Pattern) (ha : d201973 q = 1) (hb : d253272 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201973, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d201974 q = 1) (hb : d253272 q = 1) : d257209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201974, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201975 q = 1) (hb : d253272 q = 1) : d257210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201975, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201976 q = 1) (hb : d253272 q = 1) : d257211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201976, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63672 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63673 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25130 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63674 q ha hb
    | true =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
  have h23 (q : Pattern) (ha : d201978 q = 1) (hb : d253272 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d201978, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d201979 q = 1) (hb : d253272 q = 1) : d257216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d201979, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d201980 q = 1) (hb : d253272 q = 1) : d257217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201980, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d201980, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d201981 q = 1) (hb : d253272 q = 1) : d257218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201981, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d201981, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d201982 q = 1) (hb : d253272 q = 1) : d257219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201982, d257219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d201982, d257219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro63676 (p : Pattern) (ha : d201989 p = 1) (hb : d253272 p = 1) : d257224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25130 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63674 q ha hb
    | true =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
  have h2 (q : Pattern) (ha : d201978 q = 1) (hb : d253272 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201978, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201979 q = 1) (hb : d253272 q = 1) : d257216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201979, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201987 q = 1) (hb : d253272 q = 1) : d257217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201987, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201987, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201988 q = 1) (hb : d253272 q = 1) : d257218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201988, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201988, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201989 q = 1) (hb : d253272 q = 1) : d257224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201989, d257224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201989, d257224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63677 (p : Pattern) (ha : d25153 p = 1) (hb : d253272 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25148 q = 1) (hb : d253272 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63667 q ha hb
  have h2 (q : Pattern) (ha : d25105 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63667 q ha hb
    | true =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25149 q = 1) (hb : d253272 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25149, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25106 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25150 q = 1) (hb : d253272 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25150, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25151 q = 1) (hb : d253272 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25151, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25152 q = 1) (hb : d253272 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25152, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25153 q = 1) (hb : d253272 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25153, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63678 (p : Pattern) (ha : d25159 p = 1) (hb : d253272 p = 1) : d257241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25154 q = 1) (hb : d253272 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63677 q ha hb
    | true =>
      simp only [d25154, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63656 q ha hb
  have h2 (q : Pattern) (ha : d25155 q = 1) (hb : d253272 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25156 q = 1) (hb : d253272 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63656 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25157 q = 1) (hb : d253272 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25157, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25158 q = 1) (hb : d253272 q = 1) : d257240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25158, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25159 q = 1) (hb : d253272 q = 1) : d257241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25159, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro63679 (p : Pattern) (ha : d25165 p = 1) (hb : d253272 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d253272 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63678 q ha hb
    | true =>
      simp only [d25160, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d253272 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63657 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25162 q = 1) (hb : d253272 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25162, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25163 q = 1) (hb : d253272 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25163, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25164 q = 1) (hb : d253272 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25164, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25165 q = 1) (hb : d253272 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25165, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63680 (p : Pattern) (ha : d201999 p = 1) (hb : d253272 p = 1) : d257253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25166 q = 1) (hb : d253272 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63679 q ha hb
    | true =>
      simp only [d25166, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63658 q ha hb
  have h2 (q : Pattern) (ha : d201995 q = 1) (hb : d253272 q = 1) : d257249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201995, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201995, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63658 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201996 q = 1) (hb : d253272 q = 1) : d257250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201996, d257250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201996, d257250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201997 q = 1) (hb : d253272 q = 1) : d257251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201997, d257251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201997, d257251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201998 q = 1) (hb : d253272 q = 1) : d257252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201998, d257252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201998, d257252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201999 q = 1) (hb : d253272 q = 1) : d257253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201999, d257253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201999, d257253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63681 (p : Pattern) (ha : d202005 p = 1) (hb : d253272 p = 1) : d257259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63661 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63661 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63662 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201983 q = 1) (hb : d253272 q = 1) : d257220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201983, d257220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63671 q ha hb
    | true =>
      simp only [d201983, d257220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63675 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63663 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d201984 q = 1) (hb : d253272 q = 1) : d257221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201984, d257221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201984, d257221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201985 q = 1) (hb : d253272 q = 1) : d257222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201985, d257222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201985, d257222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d201986 q = 1) (hb : d253272 q = 1) : d257223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201986, d257223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201986, d257223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d201990 q = 1) (hb : d253272 q = 1) : d257225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201990, d257225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201990, d257225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63676 q ha hb
  have h12 (q : Pattern) (ha : d201991 q = 1) (hb : d253272 q = 1) : d257226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201991, d257226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201991, d257226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d201992 q = 1) (hb : d253272 q = 1) : d257227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201992, d257227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201992, d257227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d201993 q = 1) (hb : d253272 q = 1) : d257228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201993, d257228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201993, d257228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d201994 q = 1) (hb : d253272 q = 1) : d257229 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201994, d257229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201994, d257229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202000 q = 1) (hb : d253272 q = 1) : d257254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202000, d257254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202000, d257254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63680 q ha hb
  have h17 (q : Pattern) (ha : d202001 q = 1) (hb : d253272 q = 1) : d257255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202001, d257255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202001, d257255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d202002 q = 1) (hb : d253272 q = 1) : d257256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202002, d257256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202002, d257256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d202003 q = 1) (hb : d253272 q = 1) : d257257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202003, d257257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202003, d257257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d202004 q = 1) (hb : d253272 q = 1) : d257258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202004, d257258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202004, d257258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202005 q = 1) (hb : d253272 q = 1) : d257259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202005, d257259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202005, d257259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro63682 (p : Pattern) (ha : d406 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63683 (p : Pattern) (ha : d462 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63658 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63684 (p : Pattern) (ha : d25187 p = 1) (hb : d253272 p = 1) : d257269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
    | true =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d253272 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d253272 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d253272 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d253272 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25187 q = 1) (hb : d253272 q = 1) : d257269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63685 (p : Pattern) (ha : d25194 p = 1) (hb : d253272 p = 1) : d257276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
    | true =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d253272 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d253272 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d253272 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d253272 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25130 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63674 q ha hb
    | true =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
  have h7 (q : Pattern) (ha : d25190 q = 1) (hb : d253272 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25191 q = 1) (hb : d253272 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25191, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25192 q = 1) (hb : d253272 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25193 q = 1) (hb : d253272 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25194 q = 1) (hb : d253272 q = 1) : d257276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25194, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63686 (p : Pattern) (ha : d25296 p = 1) (hb : d253272 p = 1) : d257340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
    | true =>
      simp only [d25123, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d253272 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d253272 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d253272 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d253272 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63651 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25296 q = 1) (hb : d253272 q = 1) : d257340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d257340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25296, d257340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63687 (p : Pattern) (ha : d25199 p = 1) (hb : d253272 p = 1) : d257281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25198 q = 1) (hb : d253272 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25199 q = 1) (hb : d253272 q = 1) : d257281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25199, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63688 (p : Pattern) (ha : d25206 p = 1) (hb : d253272 p = 1) : d257288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25204 q = 1) (hb : d253272 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25205 q = 1) (hb : d253272 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25205, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25206 q = 1) (hb : d253272 q = 1) : d257288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25206, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63689 (p : Pattern) (ha : d312 p = 1) (hb : d253271 p = 1) : d257292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16 q = 1) (hb : d253269 q = 1) : d16 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131 q = 1) (hb : d253269 q = 1) : d40150 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d312 q = 1) (hb : d253271 q = 1) : d257292 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d253271, d257292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312, d253271, d257292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63690 (p : Pattern) (ha : d25213 p = 1) (hb : d253272 p = 1) : d257298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d253271 q = 1) : d257293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63689 q ha hb
    | true =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d253271 q = 1) : d257294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25210 q = 1) (hb : d253272 q = 1) : d257295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d133 q = 1) (hb : d253271 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63666 q ha hb
    | true =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d253271 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d253272 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25211 q = 1) (hb : d253272 q = 1) : d257296 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d257296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25211, d257296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25212 q = 1) (hb : d253272 q = 1) : d257297 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d257297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25212, d257297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63647 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d25102 q = 1) (hb : d253272 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25102, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25103 q = 1) (hb : d253272 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25103, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d25213 q = 1) (hb : d253272 q = 1) : d257298 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d257298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25213, d257298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro63691 (p : Pattern) (ha : d25221 p = 1) (hb : d253272 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d253271 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63666 q ha hb
    | true =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d253271 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9796 q = 1) (hb : d253272 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25219 q = 1) (hb : d253272 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25219, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25220 q = 1) (hb : d253272 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25220, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63647 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d22 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d25221 q = 1) (hb : d253272 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25221, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25221, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro63692 (p : Pattern) (ha : d25227 p = 1) (hb : d253272 p = 1) : d257304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d253272 q = 1) : d257299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63690 q ha hb
    | true =>
      simp only [d25214, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d253272 q = 1) : d257300 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d253272 q = 1) : d257301 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d257301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d257301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d253272 q = 1) : d257302 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d257302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d257302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25105 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63667 q ha hb
    | true =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25106 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25107 q = 1) (hb : d253272 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25108 q = 1) (hb : d253272 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25108, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25218 q = 1) (hb : d253272 q = 1) : d257303 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d257303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25218, d257303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25222 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
    | true =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25223 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25224 q = 1) (hb : d253272 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25225 q = 1) (hb : d253272 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25225, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25226 q = 1) (hb : d253272 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25226, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25227 q = 1) (hb : d253272 q = 1) : d257304 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d257304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25227, d257304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63693 (p : Pattern) (ha : d25233 p = 1) (hb : d253272 p = 1) : d257310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d253272 q = 1) : d257305 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63692 q ha hb
    | true =>
      simp only [d25228, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d253272 q = 1) : d257306 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d253272 q = 1) : d257307 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25111 q = 1) (hb : d253272 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
    | true =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
  have h5 (q : Pattern) (ha : d25112 q = 1) (hb : d253272 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25113 q = 1) (hb : d253272 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25231 q = 1) (hb : d253272 q = 1) : d257308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d257308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d257308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25114 q = 1) (hb : d253272 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25114, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25232 q = 1) (hb : d253272 q = 1) : d257309 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d257309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25232, d257309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25233 q = 1) (hb : d253272 q = 1) : d257310 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d257310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25233, d257310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro63694 (p : Pattern) (ha : d25239 p = 1) (hb : d253272 p = 1) : d257316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63693 q ha hb
    | true =>
      simp only [d25234, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d253272 q = 1) : d257314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d253272 q = 1) : d257315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25239 q = 1) (hb : d253272 q = 1) : d257316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d257316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25239, d257316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63695 (p : Pattern) (ha : d25267 p = 1) (hb : d253272 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d253272 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25267 q = 1) (hb : d253272 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25267, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63696 (p : Pattern) (ha : d202015 p = 1) (hb : d253272 p = 1) : d257322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25200 q = 1) (hb : d253272 q = 1) : d257282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63687 q ha hb
    | true =>
      simp only [d25200, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63664 q ha hb
  have h2 (q : Pattern) (ha : d25201 q = 1) (hb : d253272 q = 1) : d257283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25202 q = 1) (hb : d253272 q = 1) : d257284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25202, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25203 q = 1) (hb : d253272 q = 1) : d257285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25207 q = 1) (hb : d253272 q = 1) : d257289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63688 q ha hb
    | true =>
      simp only [d25207, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63665 q ha hb
  have h6 (q : Pattern) (ha : d25208 q = 1) (hb : d253272 q = 1) : d257290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25209 q = 1) (hb : d253272 q = 1) : d257291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25209, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25240 q = 1) (hb : d253272 q = 1) : d257317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63694 q ha hb
    | true =>
      simp only [d25240, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
  have h9 (q : Pattern) (ha : d202011 q = 1) (hb : d253272 q = 1) : d257318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d257318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202011, d257318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25268 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63695 q ha hb
    | true =>
      simp only [d25268, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25269 q = 1) (hb : d253272 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25269, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202012 q = 1) (hb : d253272 q = 1) : d257319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d257319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202012, d257319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202013 q = 1) (hb : d253272 q = 1) : d257320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d257320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202013, d257320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202014 q = 1) (hb : d253272 q = 1) : d257321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d257321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202014, d257321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202015 q = 1) (hb : d253272 q = 1) : d257322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d257322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202015, d257322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63697 (p : Pattern) (ha : d25274 p = 1) (hb : d253272 p = 1) : d257323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25198 q = 1) (hb : d253272 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25274 q = 1) (hb : d253272 q = 1) : d257323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25274, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63698 (p : Pattern) (ha : d25279 p = 1) (hb : d253272 p = 1) : d257328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63650 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25204 q = 1) (hb : d253272 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25205 q = 1) (hb : d253272 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25205, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25279 q = 1) (hb : d253272 q = 1) : d257328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25279, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63699 (p : Pattern) (ha : d25283 p = 1) (hb : d253272 p = 1) : d257332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63693 q ha hb
    | true =>
      simp only [d25234, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d253272 q = 1) : d257314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d253272 q = 1) : d257315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25283 q = 1) (hb : d253272 q = 1) : d257332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d257332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25283, d257332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63700 (p : Pattern) (ha : d25288 p = 1) (hb : d253272 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63669 q ha hb
    | true =>
      simp only [d25117, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d253272 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25288 q = 1) (hb : d253272 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25288, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63701 (p : Pattern) (ha : d202020 p = 1) (hb : d253272 p = 1) : d257338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25200 q = 1) (hb : d253272 q = 1) : d257282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63687 q ha hb
    | true =>
      simp only [d25200, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63664 q ha hb
  have h2 (q : Pattern) (ha : d25201 q = 1) (hb : d253272 q = 1) : d257283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25202 q = 1) (hb : d253272 q = 1) : d257284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25202, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25203 q = 1) (hb : d253272 q = 1) : d257285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25207 q = 1) (hb : d253272 q = 1) : d257289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63688 q ha hb
    | true =>
      simp only [d25207, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63665 q ha hb
  have h6 (q : Pattern) (ha : d25208 q = 1) (hb : d253272 q = 1) : d257290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25209 q = 1) (hb : d253272 q = 1) : d257291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25209, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25240 q = 1) (hb : d253272 q = 1) : d257317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63694 q ha hb
    | true =>
      simp only [d25240, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63670 q ha hb
  have h9 (q : Pattern) (ha : d202011 q = 1) (hb : d253272 q = 1) : d257318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d257318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202011, d257318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25268 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63695 q ha hb
    | true =>
      simp only [d25268, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25269 q = 1) (hb : d253272 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25269, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202012 q = 1) (hb : d253272 q = 1) : d257319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d257319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202012, d257319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202013 q = 1) (hb : d253272 q = 1) : d257320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d257320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202013, d257320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202014 q = 1) (hb : d253272 q = 1) : d257321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d257321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202014, d257321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25275 q = 1) (hb : d253272 q = 1) : d257324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d257324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63697 q ha hb
    | true =>
      simp only [d25275, d257324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63672 q ha hb
  have h16 (q : Pattern) (ha : d25276 q = 1) (hb : d253272 q = 1) : d257325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d257325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25276, d257325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25277 q = 1) (hb : d253272 q = 1) : d257326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d257326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25277, d257326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25278 q = 1) (hb : d253272 q = 1) : d257327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d257327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25278, d257327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25280 q = 1) (hb : d253272 q = 1) : d257329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d257329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63698 q ha hb
    | true =>
      simp only [d25280, d257329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63673 q ha hb
  have h20 (q : Pattern) (ha : d25281 q = 1) (hb : d253272 q = 1) : d257330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d257330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25281, d257330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25282 q = 1) (hb : d253272 q = 1) : d257331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d257331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25282, d257331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25284 q = 1) (hb : d253272 q = 1) : d257333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63699 q ha hb
    | true =>
      simp only [d25284, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63674 q ha hb
  have h23 (q : Pattern) (ha : d202016 q = 1) (hb : d253272 q = 1) : d257334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d257334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202016, d257334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25289 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63700 q ha hb
    | true =>
      simp only [d25289, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25290 q = 1) (hb : d253272 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25290, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202017 q = 1) (hb : d253272 q = 1) : d257335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d257335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202017, d257335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202018 q = 1) (hb : d253272 q = 1) : d257336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d257336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202018, d257336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202019 q = 1) (hb : d253272 q = 1) : d257337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d257337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202019, d257337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202020 q = 1) (hb : d253272 q = 1) : d257338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d257338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202020, d257338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro63702 (p : Pattern) (ha : d202027 p = 1) (hb : d253272 p = 1) : d257347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25284 q = 1) (hb : d253272 q = 1) : d257333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63699 q ha hb
    | true =>
      simp only [d25284, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63674 q ha hb
  have h2 (q : Pattern) (ha : d202016 q = 1) (hb : d253272 q = 1) : d257334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d257334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202016, d257334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25289 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63700 q ha hb
    | true =>
      simp only [d25289, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25290 q = 1) (hb : d253272 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25290, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202017 q = 1) (hb : d253272 q = 1) : d257335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d257335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202017, d257335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202025 q = 1) (hb : d253272 q = 1) : d257345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d257345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202025, d257345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202026 q = 1) (hb : d253272 q = 1) : d257346 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d257346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202026, d257346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d253272 q = 1) : d257347 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d257347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d257347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63703 (p : Pattern) (ha : d25319 p = 1) (hb : d253272 p = 1) : d257358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d253272 q = 1) : d257353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d257353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d257353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63690 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d253272 q = 1) : d257299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63690 q ha hb
    | true =>
      simp only [d25214, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d253272 q = 1) : d257354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d257354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d257354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d253272 q = 1) : d257300 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d253272 q = 1) : d257355 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d257355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d257355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d253272 q = 1) : d257356 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d257356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d257356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25148 q = 1) (hb : d253272 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63667 q ha hb
  have h8 (q : Pattern) (ha : d25105 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63667 q ha hb
    | true =>
      simp only [d25105, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25149 q = 1) (hb : d253272 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25149, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25106 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25106, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25150 q = 1) (hb : d253272 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25150, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25151 q = 1) (hb : d253272 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25151, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25313 q = 1) (hb : d253272 q = 1) : d257357 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d257357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25313, d257357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25314 q = 1) (hb : d253272 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
  have h15 (q : Pattern) (ha : d25222 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
    | true =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25315 q = 1) (hb : d253272 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25315, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25223 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25316 q = 1) (hb : d253272 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25316, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25317 q = 1) (hb : d253272 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25317, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25318 q = 1) (hb : d253272 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25318, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25319 q = 1) (hb : d253272 q = 1) : d257358 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d257358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25319, d257358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro63704 (p : Pattern) (ha : d25325 p = 1) (hb : d253272 p = 1) : d257364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d253272 q = 1) : d257359 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d257359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63703 q ha hb
    | true =>
      simp only [d25320, d257359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63677 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d253272 q = 1) : d257360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d257360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d257360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d253272 q = 1) : d257361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d257361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d257361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25154 q = 1) (hb : d253272 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63677 q ha hb
    | true =>
      simp only [d25154, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63656 q ha hb
  have h5 (q : Pattern) (ha : d25155 q = 1) (hb : d253272 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25156 q = 1) (hb : d253272 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25323 q = 1) (hb : d253272 q = 1) : d257362 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d257362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d257362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63656 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25157 q = 1) (hb : d253272 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25157, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25324 q = 1) (hb : d253272 q = 1) : d257363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d257363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25324, d257363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25325 q = 1) (hb : d253272 q = 1) : d257364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d257364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25325, d257364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro63705 (p : Pattern) (ha : d25331 p = 1) (hb : d253272 p = 1) : d257370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25326 q = 1) (hb : d253272 q = 1) : d257365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d257365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63704 q ha hb
    | true =>
      simp only [d25326, d257365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25327 q = 1) (hb : d253272 q = 1) : d257366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d257366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25327, d257366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25160 q = 1) (hb : d253272 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63678 q ha hb
    | true =>
      simp only [d25160, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25161 q = 1) (hb : d253272 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25328 q = 1) (hb : d253272 q = 1) : d257367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d257367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25328, d257367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25329 q = 1) (hb : d253272 q = 1) : d257368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d257368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25329, d257368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25330 q = 1) (hb : d253272 q = 1) : d257369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d257369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25330, d257369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25331 q = 1) (hb : d253272 q = 1) : d257370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d257370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25331, d257370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63706 (p : Pattern) (ha : d25356 p = 1) (hb : d253272 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d253272 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63678 q ha hb
    | true =>
      simp only [d25160, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d253272 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25353 q = 1) (hb : d253272 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25353, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25354 q = 1) (hb : d253272 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25354, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25355 q = 1) (hb : d253272 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25355, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25356 q = 1) (hb : d253272 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25356, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63707 (p : Pattern) (ha : d202037 p = 1) (hb : d253272 p = 1) : d257376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25332 q = 1) (hb : d253272 q = 1) : d257371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d257371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63705 q ha hb
    | true =>
      simp only [d25332, d257371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63679 q ha hb
  have h2 (q : Pattern) (ha : d202033 q = 1) (hb : d253272 q = 1) : d257372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d257372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202033, d257372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25357 q = 1) (hb : d253272 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63706 q ha hb
    | true =>
      simp only [d25357, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25358 q = 1) (hb : d253272 q = 1) : d257249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25358, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d253272 q = 1) : d257373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d257373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202034, d257373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d253272 q = 1) : d257374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d257374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d257374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d253272 q = 1) : d257375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d257375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d257375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d253272 q = 1) : d257376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d257376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d257376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63708 (p : Pattern) (ha : d202043 p = 1) (hb : d253272 p = 1) : d257382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25188 q = 1) (hb : d253272 q = 1) : d257270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d257270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25188, d257270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63684 q ha hb
  have h2 (q : Pattern) (ha : d25189 q = 1) (hb : d253272 q = 1) : d257271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d257271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25189, d257271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25195 q = 1) (hb : d253272 q = 1) : d257277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63684 q ha hb
    | true =>
      simp only [d25195, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63685 q ha hb
  have h4 (q : Pattern) (ha : d25196 q = 1) (hb : d253272 q = 1) : d257278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25196, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25197 q = 1) (hb : d253272 q = 1) : d257279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d257279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25197, d257279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202021 q = 1) (hb : d253272 q = 1) : d257339 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d257339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63696 q ha hb
    | true =>
      simp only [d202021, d257339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63701 q ha hb
  have h7 (q : Pattern) (ha : d25297 q = 1) (hb : d253272 q = 1) : d257341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d257341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63686 q ha hb
    | true =>
      simp only [d25297, d257341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63662 q ha hb
  have h8 (q : Pattern) (ha : d202022 q = 1) (hb : d253272 q = 1) : d257342 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d257342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202022, d257342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202023 q = 1) (hb : d253272 q = 1) : d257343 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d257343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202023, d257343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202024 q = 1) (hb : d253272 q = 1) : d257344 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d257344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202024, d257344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202028 q = 1) (hb : d253272 q = 1) : d257348 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d257348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202028, d257348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63702 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63682 q ha hb
  have h13 (q : Pattern) (ha : d202029 q = 1) (hb : d253272 q = 1) : d257349 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d257349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202029, d257349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202030 q = 1) (hb : d253272 q = 1) : d257350 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d257350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202030, d257350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202031 q = 1) (hb : d253272 q = 1) : d257351 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d257351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202031, d257351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202032 q = 1) (hb : d253272 q = 1) : d257352 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d257352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202032, d257352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202038 q = 1) (hb : d253272 q = 1) : d257377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d257377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202038, d257377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63707 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63683 q ha hb
  have h19 (q : Pattern) (ha : d202039 q = 1) (hb : d253272 q = 1) : d257378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d257378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202039, d257378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202040 q = 1) (hb : d253272 q = 1) : d257379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d257379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202040, d257379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202041 q = 1) (hb : d253272 q = 1) : d257380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d257380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202041, d257380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202042 q = 1) (hb : d253272 q = 1) : d257381 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d257381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202042, d257381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202043 q = 1) (hb : d253272 q = 1) : d257382 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d257382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202043, d257382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro63709 (p : Pattern) (ha : d202049 p = 1) (hb : d253272 p = 1) : d257388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63660 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202006 q = 1) (hb : d253272 q = 1) : d257260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202006, d257260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202006, d257260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63681 q ha hb
  have h6 (q : Pattern) (ha : d202007 q = 1) (hb : d253272 q = 1) : d257261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202007, d257261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202007, d257261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202008 q = 1) (hb : d253272 q = 1) : d257262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202008, d257262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202008, d257262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202009 q = 1) (hb : d253272 q = 1) : d257263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202009, d257263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202009, d257263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202010 q = 1) (hb : d253272 q = 1) : d257264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202010, d257264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202010, d257264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202044 q = 1) (hb : d253272 q = 1) : d257383 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d257383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202044, d257383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63708 q ha hb
  have h11 (q : Pattern) (ha : d202045 q = 1) (hb : d253272 q = 1) : d257384 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d257384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202045, d257384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202046 q = 1) (hb : d253272 q = 1) : d257385 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d257385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202046, d257385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202047 q = 1) (hb : d253272 q = 1) : d257386 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d257386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202047, d257386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202048 q = 1) (hb : d253272 q = 1) : d257387 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d257387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202048, d257387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202049 q = 1) (hb : d253272 q = 1) : d257388 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d257388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202049, d257388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63710 (p : Pattern) (ha : d25377 p = 1) (hb : d253272 p = 1) : d257310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d253272 q = 1) : d257305 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63692 q ha hb
    | true =>
      simp only [d25228, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d253272 q = 1) : d257306 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d253272 q = 1) : d257307 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25111 q = 1) (hb : d253272 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
    | true =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
  have h5 (q : Pattern) (ha : d25112 q = 1) (hb : d253272 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25113 q = 1) (hb : d253272 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25231 q = 1) (hb : d253272 q = 1) : d257308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d257308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d257308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25375 q = 1) (hb : d253272 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25375, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25376 q = 1) (hb : d253272 q = 1) : d257309 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d257309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25376, d257309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25377 q = 1) (hb : d253272 q = 1) : d257310 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d257310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25377, d257310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro63711 (p : Pattern) (ha : d25381 p = 1) (hb : d253272 p = 1) : d257200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25111 q = 1) (hb : d253272 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
    | true =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
  have h2 (q : Pattern) (ha : d25112 q = 1) (hb : d253272 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25113 q = 1) (hb : d253272 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25375 q = 1) (hb : d253272 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25375, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25380 q = 1) (hb : d253272 q = 1) : d257199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25380, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25381 q = 1) (hb : d253272 q = 1) : d257200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25381, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63712 (p : Pattern) (ha : d25387 p = 1) (hb : d253272 p = 1) : d257316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d253272 q = 1) : d257314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d253272 q = 1) : d257315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25387 q = 1) (hb : d253272 q = 1) : d257316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d257316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25387, d257316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63713 (p : Pattern) (ha : d25391 p = 1) (hb : d253272 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d253272 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25391 q = 1) (hb : d253272 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25391, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63714 (p : Pattern) (ha : d25397 p = 1) (hb : d253272 p = 1) : d257393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d253272 q = 1) : d257317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63712 q ha hb
    | true =>
      simp only [d25392, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63713 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d253272 q = 1) : d257389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d257389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d257389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d253272 q = 1) : d257390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d257390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d257390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d253272 q = 1) : d257391 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d257391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d257391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d253272 q = 1) : d257392 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d257392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d257392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25397 q = 1) (hb : d253272 q = 1) : d257393 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d257393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25397, d257393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63715 (p : Pattern) (ha : d25400 p = 1) (hb : d253272 p = 1) : d257332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d253272 q = 1) : d257314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d253272 q = 1) : d257315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d257315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25400 q = 1) (hb : d253272 q = 1) : d257332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d257332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25400, d257332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63716 (p : Pattern) (ha : d25401 p = 1) (hb : d253272 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d253272 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25401 q = 1) (hb : d253272 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25401, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63717 (p : Pattern) (ha : d25407 p = 1) (hb : d253272 p = 1) : d257400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d253272 q = 1) : d257317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63712 q ha hb
    | true =>
      simp only [d25392, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63713 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d253272 q = 1) : d257389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d257389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d257389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d253272 q = 1) : d257390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d257390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d257390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d253272 q = 1) : d257391 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d257391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d257391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d253272 q = 1) : d257392 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d257392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d257392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25402 q = 1) (hb : d253272 q = 1) : d257333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63715 q ha hb
    | true =>
      simp only [d25402, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63716 q ha hb
  have h7 (q : Pattern) (ha : d25403 q = 1) (hb : d253272 q = 1) : d257396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d257396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d257396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25404 q = 1) (hb : d253272 q = 1) : d257397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d257397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25404, d257397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25405 q = 1) (hb : d253272 q = 1) : d257398 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d257398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d257398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25406 q = 1) (hb : d253272 q = 1) : d257399 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d257399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d257399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25407 q = 1) (hb : d253272 q = 1) : d257400 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d257400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25407, d257400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63718 (p : Pattern) (ha : d25556 p = 1) (hb : d253272 p = 1) : d257481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d253272 q = 1) : d257317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63712 q ha hb
    | true =>
      simp only [d25392, d257317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63713 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d253272 q = 1) : d257389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d257389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d257389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d253272 q = 1) : d257390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d257390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d257390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d253272 q = 1) : d257391 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d257391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d257391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d253272 q = 1) : d257392 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d257392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d257392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25551 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63713 q ha hb
    | true =>
      simp only [d25551, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25552 q = 1) (hb : d253272 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25553 q = 1) (hb : d253272 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25553, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25554 q = 1) (hb : d253272 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25555 q = 1) (hb : d253272 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25556 q = 1) (hb : d253272 q = 1) : d257481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25556, d257481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25556, d257481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63719 (p : Pattern) (ha : d25562 p = 1) (hb : d253272 p = 1) : d257276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25551 q = 1) (hb : d253272 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63713 q ha hb
    | true =>
      simp only [d25551, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25552 q = 1) (hb : d253272 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25553 q = 1) (hb : d253272 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25553, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25554 q = 1) (hb : d253272 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25555 q = 1) (hb : d253272 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25557 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63716 q ha hb
    | true =>
      simp only [d25557, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25558 q = 1) (hb : d253272 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25559 q = 1) (hb : d253272 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25559, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25560 q = 1) (hb : d253272 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25561 q = 1) (hb : d253272 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25562 q = 1) (hb : d253272 q = 1) : d257276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25562, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25562, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63720 (p : Pattern) (ha : d25571 p = 1) (hb : d253272 p = 1) : d257490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25557 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63716 q ha hb
    | true =>
      simp only [d25557, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25558 q = 1) (hb : d253272 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25559 q = 1) (hb : d253272 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25559, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25560 q = 1) (hb : d253272 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25561 q = 1) (hb : d253272 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25571 q = 1) (hb : d253272 q = 1) : d257490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25571, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25571, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63721 (p : Pattern) (ha : d25614 p = 1) (hb : d253272 p = 1) : d257241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25154 q = 1) (hb : d253272 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63677 q ha hb
    | true =>
      simp only [d25154, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63656 q ha hb
  have h2 (q : Pattern) (ha : d25155 q = 1) (hb : d253272 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25156 q = 1) (hb : d253272 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25604 q = 1) (hb : d253272 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25604, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25613 q = 1) (hb : d253272 q = 1) : d257240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25613, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25613, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25614 q = 1) (hb : d253272 q = 1) : d257241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25614, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25614, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63722 (p : Pattern) (ha : d25670 p = 1) (hb : d253272 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25615 q = 1) (hb : d253272 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63721 q ha hb
    | true =>
      simp only [d25615, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25616 q = 1) (hb : d253272 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25667 q = 1) (hb : d253272 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25667, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25667, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25668 q = 1) (hb : d253272 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25668, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25668, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25669 q = 1) (hb : d253272 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25669, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25669, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25670 q = 1) (hb : d253272 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25670, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25670, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63723 (p : Pattern) (ha : d25676 p = 1) (hb : d253272 p = 1) : d257536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25671 q = 1) (hb : d253272 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25671, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63722 q ha hb
    | true =>
      simp only [d25671, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25672 q = 1) (hb : d253272 q = 1) : d257532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25672, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25672, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25673 q = 1) (hb : d253272 q = 1) : d257533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25673, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25673, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25674 q = 1) (hb : d253272 q = 1) : d257534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25674, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25674, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25675 q = 1) (hb : d253272 q = 1) : d257535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25675, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25675, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25676 q = 1) (hb : d253272 q = 1) : d257536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25676, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25676, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63724 (p : Pattern) (ha : d25412 p = 1) (hb : d253272 p = 1) : d257405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d253272 q = 1) : d257314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d253272 q = 1) : d257404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d257404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d257404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25412 q = 1) (hb : d253272 q = 1) : d257405 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d257405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25412, d257405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63725 (p : Pattern) (ha : d25414 p = 1) (hb : d253272 p = 1) : d257281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d253272 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25414 q = 1) (hb : d253272 q = 1) : d257281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25414, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63726 (p : Pattern) (ha : d25421 p = 1) (hb : d253272 p = 1) : d257412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d253272 q = 1) : d257410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d257410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d257410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d253272 q = 1) : d257411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d257411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d257411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25421 q = 1) (hb : d253272 q = 1) : d257412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d257412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25421, d257412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63727 (p : Pattern) (ha : d25424 p = 1) (hb : d253272 p = 1) : d257288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d253272 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d253272 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25424 q = 1) (hb : d253272 q = 1) : d257288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25424, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63728 (p : Pattern) (ha : d530 p = 1) (hb : d253271 p = 1) : d257416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d529 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d311 q = 1) (hb : d253269 q = 1) : d40263 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d40263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d311, d40263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d530 q = 1) (hb : d253271 q = 1) : d257416 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d530, d253271, d257416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d530, d253271, d257416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63729 (p : Pattern) (ha : d536 p = 1) (hb : d253271 p = 1) : d257292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16 q = 1) (hb : d253269 q = 1) : d16 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131 q = 1) (hb : d253269 q = 1) : d40150 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d536 q = 1) (hb : d253271 q = 1) : d257292 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d536, d253271, d257292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d536, d253271, d257292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63730 (p : Pattern) (ha : d25432 p = 1) (hb : d253271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25432 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d25432, d253271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25432, d253271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro63731 (p : Pattern) (ha : d25438 p = 1) (hb : d253272 p = 1) : d257424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d253271 q = 1) : d257417 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d257417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63728 q ha hb
    | true =>
      simp only [d531, d257417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d253271 q = 1) : d257418 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d257418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d257418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25428 q = 1) (hb : d253272 q = 1) : d257419 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d253272, d257419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25428, d253272, d257419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d537 q = 1) (hb : d253271 q = 1) : d257293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63729 q ha hb
    | true =>
      simp only [d537, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d538 q = 1) (hb : d253271 q = 1) : d257294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d538, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25429 q = 1) (hb : d253272 q = 1) : d257295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25429, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25429, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25430 q = 1) (hb : d253272 q = 1) : d257420 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d257420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25430, d257420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25431 q = 1) (hb : d253272 q = 1) : d257421 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d257421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25431, d257421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d313 q = 1) (hb : d253271 q = 1) : d257293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63689 q ha hb
    | true =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d253271 q = 1) : d257294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25210 q = 1) (hb : d253272 q = 1) : d257295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d25433 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63730 q ha hb
    | true =>
      simp only [d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25434 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25435 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25435, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25435, d253272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d25436 q = 1) (hb : d253272 q = 1) : d257422 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25436, d257422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25436, d257422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25437 q = 1) (hb : d253272 q = 1) : d257423 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25437, d257423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d25437, d257423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h19 (q : Pattern) (ha : d25438 q = 1) (hb : d253272 q = 1) : d257424 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d257424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25438, d257424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63732 (p : Pattern) (ha : d25443 p = 1) (hb : d253272 p = 1) : d257298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d253271 q = 1) : d257293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63689 q ha hb
    | true =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d253271 q = 1) : d257294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25210 q = 1) (hb : d253272 q = 1) : d257295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d133 q = 1) (hb : d253271 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63666 q ha hb
    | true =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d253271 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d253272 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25211 q = 1) (hb : d253272 q = 1) : d257296 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d257296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25211, d257296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25212 q = 1) (hb : d253272 q = 1) : d257297 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d257297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25212, d257297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25219 q = 1) (hb : d253272 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25219, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h12 (q : Pattern) (ha : d25220 q = 1) (hb : d253272 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25220, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h13 (q : Pattern) (ha : d25443 q = 1) (hb : d253272 q = 1) : d257298 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d257298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25443, d257298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro63733 (p : Pattern) (ha : d25451 p = 1) (hb : d253272 p = 1) : d257430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d253271 q = 1) : d257293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63689 q ha hb
    | true =>
      simp only [d313, d257293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d253271 q = 1) : d257294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d257294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25210 q = 1) (hb : d253272 q = 1) : d257295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25210, d253272, d257295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25449 q = 1) (hb : d253272 q = 1) : d257422 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d257422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25449, d257422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25450 q = 1) (hb : d253272 q = 1) : d257423 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, d257423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25450, d257423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d133 q = 1) (hb : d253271 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63666 q ha hb
    | true =>
      simp only [d133, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d134 q = 1) (hb : d253271 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9796 q = 1) (hb : d253272 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9796, d253272, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d25219 q = 1) (hb : d253272 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25219, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d25220 q = 1) (hb : d253272 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25220, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d25451 q = 1) (hb : d253272 q = 1) : d257430 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25451, d257430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25451, d257430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro63734 (p : Pattern) (ha : d25457 p = 1) (hb : d253272 p = 1) : d257436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d253272 q = 1) : d257425 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d257425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63731 q ha hb
    | true =>
      simp only [d25439, d257425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d253272 q = 1) : d257426 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d257426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d257426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d253272 q = 1) : d257427 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d257427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d257427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d253272 q = 1) : d257428 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d257428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d257428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d253272 q = 1) : d257299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63732 q ha hb
    | true =>
      simp only [d25444, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d253272 q = 1) : d257300 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d253272 q = 1) : d257301 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d257301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d257301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d253272 q = 1) : d257302 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d257302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d257302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d253272 q = 1) : d257429 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d257429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d257429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25452 q = 1) (hb : d253272 q = 1) : d257431 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d257431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63733 q ha hb
    | true =>
      simp only [d25452, d257431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25453 q = 1) (hb : d253272 q = 1) : d257432 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d257432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25453, d257432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25454 q = 1) (hb : d253272 q = 1) : d257433 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d257433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d257433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25455 q = 1) (hb : d253272 q = 1) : d257434 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d257434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25455, d257434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25222 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
    | true =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25223 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25224 q = 1) (hb : d253272 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25225 q = 1) (hb : d253272 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25225, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25456 q = 1) (hb : d253272 q = 1) : d257435 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25456, d257435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25456, d257435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25457 q = 1) (hb : d253272 q = 1) : d257436 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d257436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25457, d257436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro63735 (p : Pattern) (ha : d25461 p = 1) (hb : d253272 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25222 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
    | true =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25223 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25224 q = 1) (hb : d253272 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25225 q = 1) (hb : d253272 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25225, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25226 q = 1) (hb : d253272 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25226, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25461 q = 1) (hb : d253272 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25461, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25461, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro63736 (p : Pattern) (ha : d25467 p = 1) (hb : d253272 p = 1) : d257442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25458 q = 1) (hb : d253272 q = 1) : d257437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d257437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63734 q ha hb
    | true =>
      simp only [d25458, d257437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63692 q ha hb
  have h2 (q : Pattern) (ha : d25459 q = 1) (hb : d253272 q = 1) : d257438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d257438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25459, d257438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25460 q = 1) (hb : d253272 q = 1) : d257439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d257439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25460, d257439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25462 q = 1) (hb : d253272 q = 1) : d257305 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63692 q ha hb
    | true =>
      simp only [d25462, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63735 q ha hb
  have h5 (q : Pattern) (ha : d25463 q = 1) (hb : d253272 q = 1) : d257306 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25463, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25464 q = 1) (hb : d253272 q = 1) : d257307 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25464, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25465 q = 1) (hb : d253272 q = 1) : d257440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d257440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25465, d257440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25228 q = 1) (hb : d253272 q = 1) : d257305 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63692 q ha hb
    | true =>
      simp only [d25228, d257305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
  have h9 (q : Pattern) (ha : d25229 q = 1) (hb : d253272 q = 1) : d257306 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d257306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25230 q = 1) (hb : d253272 q = 1) : d257307 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d257307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25111 q = 1) (hb : d253272 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63668 q ha hb
    | true =>
      simp only [d25111, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63649 q ha hb
  have h12 (q : Pattern) (ha : d25112 q = 1) (hb : d253272 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25113 q = 1) (hb : d253272 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25231 q = 1) (hb : d253272 q = 1) : d257308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d257308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25231, d257308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25466 q = 1) (hb : d253272 q = 1) : d257441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d257441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25466, d257441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25467 q = 1) (hb : d253272 q = 1) : d257442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d257442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25467, d257442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro63737 (p : Pattern) (ha : d25473 p = 1) (hb : d253272 p = 1) : d257448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d253272 q = 1) : d257443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d257443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63736 q ha hb
    | true =>
      simp only [d25468, d257443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d253272 q = 1) : d257444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d257444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d257444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d253272 q = 1) : d257445 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d257445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d257445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d253272 q = 1) : d257446 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d257446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d257446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d253272 q = 1) : d257447 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d257447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d257447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25473 q = 1) (hb : d253272 q = 1) : d257448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d257448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25473, d257448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63738 (p : Pattern) (ha : d25519 p = 1) (hb : d253272 p = 1) : d257454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d253272 q = 1) : d257451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d257451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d257451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d253272 q = 1) : d257452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d257452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d257452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d253272 q = 1) : d257453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d257453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d257453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25519 q = 1) (hb : d253272 q = 1) : d257454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25519, d257454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25519, d257454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro63739 (p : Pattern) (ha : d202054 p = 1) (hb : d253272 p = 1) : d257460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d253272 q = 1) : d257406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d257406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63724 q ha hb
    | true =>
      simp only [d25415, d257406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63725 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d253272 q = 1) : d257407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d257407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d257407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d253272 q = 1) : d257408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d257408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d257408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d253272 q = 1) : d257409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d257409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d257409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d253272 q = 1) : d257413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d257413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63726 q ha hb
    | true =>
      simp only [d25425, d257413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63727 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d253272 q = 1) : d257414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d257414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d257414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d253272 q = 1) : d257415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d257415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d257415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d253272 q = 1) : d257449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d257449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63737 q ha hb
    | true =>
      simp only [d25474, d257449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63712 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d253272 q = 1) : d257450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d257450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d257450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d253272 q = 1) : d257455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d257455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63738 q ha hb
    | true =>
      simp only [d25520, d257455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d253272 q = 1) : d257456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d257456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d257456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d253272 q = 1) : d257457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d257457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d257457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d253272 q = 1) : d257458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d257458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d257458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d253272 q = 1) : d257459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d257459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d257459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202054 q = 1) (hb : d253272 q = 1) : d257460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d257460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d257460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro63740 (p : Pattern) (ha : d25526 p = 1) (hb : d253272 p = 1) : d257461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d253272 q = 1) : d257314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d257314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d253272 q = 1) : d257404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d257404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d257404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25526 q = 1) (hb : d253272 q = 1) : d257461 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25526, d257461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25526, d257461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63741 (p : Pattern) (ha : d25527 p = 1) (hb : d253272 p = 1) : d257323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d253272 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d253272 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25527 q = 1) (hb : d253272 q = 1) : d257323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25527, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25527, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63742 (p : Pattern) (ha : d25532 p = 1) (hb : d253272 p = 1) : d257466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d253272 q = 1) : d257313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d257313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d253272 q = 1) : d257410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d257410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d257410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d253272 q = 1) : d257411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d257411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d257411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25532 q = 1) (hb : d253272 q = 1) : d257466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25532, d257466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25532, d257466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63743 (p : Pattern) (ha : d25533 p = 1) (hb : d253272 p = 1) : d257328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d253272 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63711 q ha hb
    | true =>
      simp only [d25382, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d253272 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d253272 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d253272 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d253272 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25533 q = 1) (hb : d253272 q = 1) : d257328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25533, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25533, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63744 (p : Pattern) (ha : d25537 p = 1) (hb : d253272 p = 1) : d257470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d253272 q = 1) : d257443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d257443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63736 q ha hb
    | true =>
      simp only [d25468, d257443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d253272 q = 1) : d257444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d257444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d257444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d253272 q = 1) : d257445 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d257445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d257445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d253272 q = 1) : d257446 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d257446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d257446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d253272 q = 1) : d257447 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d257447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d257447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25537 q = 1) (hb : d253272 q = 1) : d257470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25537, d257470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25537, d257470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro63745 (p : Pattern) (ha : d25543 p = 1) (hb : d253272 p = 1) : d257473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d253272 q = 1) : d257311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63710 q ha hb
    | true =>
      simp only [d25378, d257311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d253272 q = 1) : d257312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d257312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d253272 q = 1) : d257451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d257451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d257451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d253272 q = 1) : d257452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d257452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d257452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d253272 q = 1) : d257453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d257453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d257453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25543 q = 1) (hb : d253272 q = 1) : d257473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25543, d257473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25543, d257473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro63746 (p : Pattern) (ha : d202059 p = 1) (hb : d253272 p = 1) : d257479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d253272 q = 1) : d257406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d257406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63724 q ha hb
    | true =>
      simp only [d25415, d257406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63725 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d253272 q = 1) : d257407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d257407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d257407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d253272 q = 1) : d257408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d257408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d257408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d253272 q = 1) : d257409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d257409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d257409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d253272 q = 1) : d257413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d257413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63726 q ha hb
    | true =>
      simp only [d25425, d257413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63727 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d253272 q = 1) : d257414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d257414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d257414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d253272 q = 1) : d257415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d257415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d257415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d253272 q = 1) : d257449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d257449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63737 q ha hb
    | true =>
      simp only [d25474, d257449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63712 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d253272 q = 1) : d257450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d257450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d257450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d253272 q = 1) : d257455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d257455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63738 q ha hb
    | true =>
      simp only [d25520, d257455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d253272 q = 1) : d257456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d257456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d257456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d253272 q = 1) : d257457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d257457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d257457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d253272 q = 1) : d257458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d257458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d257458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d253272 q = 1) : d257459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d257459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d257459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25528 q = 1) (hb : d253272 q = 1) : d257462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25528, d257462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63740 q ha hb
    | true =>
      simp only [d25528, d257462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63741 q ha hb
  have h16 (q : Pattern) (ha : d25529 q = 1) (hb : d253272 q = 1) : d257463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25529, d257463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25529, d257463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25530 q = 1) (hb : d253272 q = 1) : d257464 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25530, d257464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25530, d257464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25531 q = 1) (hb : d253272 q = 1) : d257465 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25531, d257465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25531, d257465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25534 q = 1) (hb : d253272 q = 1) : d257467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25534, d257467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63742 q ha hb
    | true =>
      simp only [d25534, d257467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63743 q ha hb
  have h20 (q : Pattern) (ha : d25535 q = 1) (hb : d253272 q = 1) : d257468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25535, d257468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25535, d257468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25536 q = 1) (hb : d253272 q = 1) : d257469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25536, d257469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25536, d257469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25538 q = 1) (hb : d253272 q = 1) : d257471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d257471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63744 q ha hb
    | true =>
      simp only [d25538, d257471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63715 q ha hb
  have h23 (q : Pattern) (ha : d202055 q = 1) (hb : d253272 q = 1) : d257472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d257472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202055, d257472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25544 q = 1) (hb : d253272 q = 1) : d257474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d257474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63745 q ha hb
    | true =>
      simp only [d25544, d257474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25545 q = 1) (hb : d253272 q = 1) : d257475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d257475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25545, d257475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202056 q = 1) (hb : d253272 q = 1) : d257476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d257476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202056, d257476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202057 q = 1) (hb : d253272 q = 1) : d257477 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d257477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202057, d257477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202058 q = 1) (hb : d253272 q = 1) : d257478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d257478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202058, d257478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202059 q = 1) (hb : d253272 q = 1) : d257479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d257479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202059, d257479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro63747 (p : Pattern) (ha : d202066 p = 1) (hb : d253272 p = 1) : d257488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25538 q = 1) (hb : d253272 q = 1) : d257471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d257471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63744 q ha hb
    | true =>
      simp only [d25538, d257471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63715 q ha hb
  have h2 (q : Pattern) (ha : d202055 q = 1) (hb : d253272 q = 1) : d257472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d257472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202055, d257472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25544 q = 1) (hb : d253272 q = 1) : d257474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d257474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63745 q ha hb
    | true =>
      simp only [d25544, d257474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25545 q = 1) (hb : d253272 q = 1) : d257475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d257475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25545, d257475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d253272 q = 1) : d257476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d257476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202056, d257476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d253272 q = 1) : d257486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d257486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d257486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d253272 q = 1) : d257487 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d257487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d257487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d253272 q = 1) : d257488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d257488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d257488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro63748 (p : Pattern) (ha : d25591 p = 1) (hb : d253272 p = 1) : d257506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d253272 q = 1) : d257496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d257496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d257496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63731 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d253272 q = 1) : d257425 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d257425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63731 q ha hb
    | true =>
      simp only [d25439, d257425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d253272 q = 1) : d257497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d257497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d257497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d253272 q = 1) : d257426 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d257426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d257426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d253272 q = 1) : d257498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d257498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d257498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d253272 q = 1) : d257499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d257499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d257499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d253272 q = 1) : d257353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d257353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d257353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63732 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d253272 q = 1) : d257299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63732 q ha hb
    | true =>
      simp only [d25444, d257299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d253272 q = 1) : d257354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d257354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d257354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d253272 q = 1) : d257300 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d257300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d253272 q = 1) : d257355 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d257355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d257355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d253272 q = 1) : d257356 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d257356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d257356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d253272 q = 1) : d257500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d257500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d257500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25586 q = 1) (hb : d253272 q = 1) : d257501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d257501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d257501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63733 q ha hb
  have h15 (q : Pattern) (ha : d25452 q = 1) (hb : d253272 q = 1) : d257431 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d257431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63733 q ha hb
    | true =>
      simp only [d25452, d257431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25587 q = 1) (hb : d253272 q = 1) : d257502 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d257502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25587, d257502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25453 q = 1) (hb : d253272 q = 1) : d257432 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d257432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25453, d257432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25588 q = 1) (hb : d253272 q = 1) : d257503 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d257503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25588, d257503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25589 q = 1) (hb : d253272 q = 1) : d257504 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d257504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25589, d257504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d25314 q = 1) (hb : d253272 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
  have h21 (q : Pattern) (ha : d25222 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
    | true =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25315 q = 1) (hb : d253272 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25315, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d25223 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25316 q = 1) (hb : d253272 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d25316, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25317 q = 1) (hb : d253272 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25317, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25590 q = 1) (hb : d253272 q = 1) : d257505 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25590, d257505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25590, d257505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25591 q = 1) (hb : d253272 q = 1) : d257506 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25591, d257506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25591, d257506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro63749 (p : Pattern) (ha : d25595 p = 1) (hb : d253272 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25314 q = 1) (hb : d253272 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
  have h2 (q : Pattern) (ha : d25222 q = 1) (hb : d253272 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63691 q ha hb
    | true =>
      simp only [d25222, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25315 q = 1) (hb : d253272 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25315, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25223 q = 1) (hb : d253272 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25223, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25316 q = 1) (hb : d253272 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25316, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25317 q = 1) (hb : d253272 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25317, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63648 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25318 q = 1) (hb : d253272 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25318, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25595 q = 1) (hb : d253272 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25595, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25595, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
