import NetHack.Soko22Hazard87.AndIntroBlocks0372
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro93250 (p : Pattern) (ha : d341743 p = 1) (hb : d343352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341733 q = 1) (hb : d343342 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341733, d343342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93247 q ha hb
    | true =>
      simp only [d341733, d343342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93248 q ha hb
  have h2 (q : Pattern) (ha : d341734 q = 1) (hb : d343343 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341734, d343343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341734, d343343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341735 q = 1) (hb : d343344 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341735, d343344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341735, d343344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341737 q = 1) (hb : d343346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341737, d343346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341737, d343346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341742 q = 1) (hb : d343351 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d341742, d343351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341742, d343351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341743 q = 1) (hb : d343352 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d341743, d343352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341743, d343352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93251 (p : Pattern) (ha : d341749 p = 1) (hb : d343358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341746 q = 1) (hb : d343355 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341747 q = 1) (hb : d343356 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341748 q = 1) (hb : d343357 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341748, d343357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341748, d343357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341749 q = 1) (hb : d343358 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341749, d343358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341749, d343358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93252 (p : Pattern) (ha : d341753 p = 1) (hb : d343362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341750 q = 1) (hb : d343359 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341751 q = 1) (hb : d343360 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341752 q = 1) (hb : d343361 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341752, d343361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341752, d343361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341753 q = 1) (hb : d343362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341753, d343362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341753, d343362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93253 (p : Pattern) (ha : d341759 p = 1) (hb : d343368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341754 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
    | true =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
  have h2 (q : Pattern) (ha : d341755 q = 1) (hb : d343364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341755, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341755, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341756 q = 1) (hb : d343365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341756, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341756, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341757 q = 1) (hb : d343366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341757, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341757, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341758 q = 1) (hb : d343367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341758, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341758, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341759 q = 1) (hb : d343368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341759, d343368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341759, d343368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93254 (p : Pattern) (ha : d341762 p = 1) (hb : d343371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341746 q = 1) (hb : d343355 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341747 q = 1) (hb : d343356 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341748 q = 1) (hb : d343357 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341748, d343357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341748, d343357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341762 q = 1) (hb : d343371 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341762, d343371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341762, d343371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93255 (p : Pattern) (ha : d341763 p = 1) (hb : d343372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341750 q = 1) (hb : d343359 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341751 q = 1) (hb : d343360 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341752 q = 1) (hb : d343361 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341752, d343361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341752, d343361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341763 q = 1) (hb : d343372 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341763, d343372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341763, d343372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93256 (p : Pattern) (ha : d341769 p = 1) (hb : d343378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341754 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
    | true =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
  have h2 (q : Pattern) (ha : d341755 q = 1) (hb : d343364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341755, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341755, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341756 q = 1) (hb : d343365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341756, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341756, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341757 q = 1) (hb : d343366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341757, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341757, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341758 q = 1) (hb : d343367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341758, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341758, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341764 q = 1) (hb : d343373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341764, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93254 q ha hb
    | true =>
      simp only [d341764, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93255 q ha hb
  have h7 (q : Pattern) (ha : d341765 q = 1) (hb : d343374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341765, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341765, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341766 q = 1) (hb : d343375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341766, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341766, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341767 q = 1) (hb : d343376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341767, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341767, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341768 q = 1) (hb : d343377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341768, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341768, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341769 q = 1) (hb : d343378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341769, d343378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341769, d343378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93257 (p : Pattern) (ha : d341774 p = 1) (hb : d343383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341746 q = 1) (hb : d343355 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341747 q = 1) (hb : d343356 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341773 q = 1) (hb : d343382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341773, d343382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341773, d343382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341774 q = 1) (hb : d343383 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341774, d343383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341774, d343383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93258 (p : Pattern) (ha : d341776 p = 1) (hb : d343385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341750 q = 1) (hb : d343359 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341751 q = 1) (hb : d343360 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341775 q = 1) (hb : d343384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341775, d343384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341775, d343384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341776 q = 1) (hb : d343385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341776, d343385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341776, d343385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93259 (p : Pattern) (ha : d341783 p = 1) (hb : d343392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341746 q = 1) (hb : d343355 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341781 q = 1) (hb : d343390 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341781, d343390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341781, d343390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341782 q = 1) (hb : d343391 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341782, d343391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341782, d343391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341783 q = 1) (hb : d343392 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341783, d343392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341783, d343392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93260 (p : Pattern) (ha : d341786 p = 1) (hb : d343395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341750 q = 1) (hb : d343359 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341784 q = 1) (hb : d343393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341784, d343393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341784, d343393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341785 q = 1) (hb : d343394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341785, d343394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341785, d343394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341786 q = 1) (hb : d343395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341786, d343395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341786, d343395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93261 (p : Pattern) (ha : d341790 p = 1) (hb : d343399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2001 q = 1) (hb : d341328 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d341328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d341328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341521 q = 1) (hb : d343134 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d341521, d343134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341521, d343134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d341790 q = 1) (hb : d343399 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d341790, d343399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341790, d343399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93262 (p : Pattern) (ha : d341799 p = 1) (hb : d343408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341791 q = 1) (hb : d343400 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93261 q ha hb
    | true =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341792 q = 1) (hb : d343401 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341523 q = 1) (hb : d343136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341523, d343136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93210 q ha hb
    | true =>
      simp only [d341523, d343136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341524 q = 1) (hb : d343137 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341524, d343137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341524, d343137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341793 q = 1) (hb : d343402 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341793, d343402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341793, d343402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341794 q = 1) (hb : d343403 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341794, d343403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341794, d343403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341795 q = 1) (hb : d343404 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d341795, d343404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341795, d343404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341331 q = 1) (hb : d342944 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341331, d342944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93172 q ha hb
    | true =>
      simp only [d341331, d342944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341332 q = 1) (hb : d342945 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341332, d342945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341332, d342945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d341525 q = 1) (hb : d343138 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341525, d343138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341525, d343138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341796 q = 1) (hb : d343405 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341796, d343405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341796, d343405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341797 q = 1) (hb : d343406 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341797, d343406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341797, d343406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d341798 q = 1) (hb : d343407 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d341798, d343407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341798, d343407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d341799 q = 1) (hb : d343408 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d341799, d343408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341799, d343408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro93263 (p : Pattern) (ha : d341804 p = 1) (hb : d343413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341523 q = 1) (hb : d343136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341523, d343136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93210 q ha hb
    | true =>
      simp only [d341523, d343136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341524 q = 1) (hb : d343137 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341524, d343137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341524, d343137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341331 q = 1) (hb : d342944 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341331, d342944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93172 q ha hb
    | true =>
      simp only [d341331, d342944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341332 q = 1) (hb : d342945 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341332, d342945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341332, d342945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341525 q = 1) (hb : d343138 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341525, d343138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341525, d343138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341529 q = 1) (hb : d343141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341529, d343141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93211 q ha hb
    | true =>
      simp only [d341529, d343141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341530 q = 1) (hb : d343142 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341530, d343142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341530, d343142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d341535 q = 1) (hb : d343145 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341535, d343145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341535, d343145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341536 q = 1) (hb : d343146 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341536, d343146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341536, d343146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341537 q = 1) (hb : d343147 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d341537, d343147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341537, d343147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341205 q = 1) (hb : d342819 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341205, d342819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93150 q ha hb
    | true =>
      simp only [d341205, d342819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d341206 q = 1) (hb : d342820 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341206, d342820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341206, d342820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d341333 q = 1) (hb : d342946 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341333, d342946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341333, d342946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d341552 q = 1) (hb : d343162 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341552, d343162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341552, d343162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d341553 q = 1) (hb : d343163 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d341553, d343163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341553, d343163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d341804 q = 1) (hb : d343413 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d341804, d343413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341804, d343413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93264 (p : Pattern) (ha : d341812 p = 1) (hb : d343421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341523 q = 1) (hb : d343136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341523, d343136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93210 q ha hb
    | true =>
      simp only [d341523, d343136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341524 q = 1) (hb : d343137 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341524, d343137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341524, d343137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341331 q = 1) (hb : d342944 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341331, d342944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93172 q ha hb
    | true =>
      simp only [d341331, d342944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341332 q = 1) (hb : d342945 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341332, d342945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341332, d342945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341525 q = 1) (hb : d343138 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341525, d343138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341525, d343138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341810 q = 1) (hb : d343419 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341810, d343419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341810, d343419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341811 q = 1) (hb : d343420 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d341811, d343420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341811, d343420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341205 q = 1) (hb : d342819 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341205, d342819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93150 q ha hb
    | true =>
      simp only [d341205, d342819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341206 q = 1) (hb : d342820 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341206, d342820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341206, d342820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d341333 q = 1) (hb : d342946 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341333, d342946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341333, d342946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341552 q = 1) (hb : d343162 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341552, d343162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341552, d343162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d341553 q = 1) (hb : d343163 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d341553, d343163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341553, d343163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341812 q = 1) (hb : d343421 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d341812, d343421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341812, d343421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro93265 (p : Pattern) (ha : d341818 p = 1) (hb : d343427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341800 q = 1) (hb : d343409 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341800, d343409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93262 q ha hb
    | true =>
      simp only [d341800, d343409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341801 q = 1) (hb : d343410 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341801, d343410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341801, d343410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341802 q = 1) (hb : d343411 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341802, d343411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341802, d343411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341803 q = 1) (hb : d343412 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341803, d343412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341803, d343412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341805 q = 1) (hb : d343414 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341805, d343414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93263 q ha hb
    | true =>
      simp only [d341805, d343414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341806 q = 1) (hb : d343415 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341806, d343415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341806, d343415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341807 q = 1) (hb : d343416 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341807, d343416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341807, d343416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341808 q = 1) (hb : d343417 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341808, d343417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341808, d343417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341809 q = 1) (hb : d343418 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341809, d343418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341809, d343418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341813 q = 1) (hb : d343422 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341813, d343422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93264 q ha hb
    | true =>
      simp only [d341813, d343422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d341814 q = 1) (hb : d343423 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341814, d343423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341814, d343423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d341815 q = 1) (hb : d343424 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341815, d343424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341815, d343424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d341816 q = 1) (hb : d343425 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341816, d343425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341816, d343425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d341555 q = 1) (hb : d343165 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
    | true =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d341556 q = 1) (hb : d343166 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d341557 q = 1) (hb : d343167 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341557, d343167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341557, d343167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341558 q = 1) (hb : d343168 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341558, d343168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341558, d343168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d341817 q = 1) (hb : d343426 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341817, d343426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341817, d343426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d341818 q = 1) (hb : d343427 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341818, d343427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341818, d343427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93266 (p : Pattern) (ha : d341822 p = 1) (hb : d343431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341555 q = 1) (hb : d343165 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
    | true =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341556 q = 1) (hb : d343166 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341557 q = 1) (hb : d343167 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341557, d343167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341557, d343167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341558 q = 1) (hb : d343168 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341558, d343168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341558, d343168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341720 q = 1) (hb : d343329 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
    | true =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341721 q = 1) (hb : d343330 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341722 q = 1) (hb : d343331 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341722, d343331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341722, d343331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341723 q = 1) (hb : d343332 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341723, d343332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341723, d343332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341724 q = 1) (hb : d343333 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341724, d343333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341724, d343333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341727 q = 1) (hb : d343336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341727, d343336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341727, d343336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d341822 q = 1) (hb : d343431 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341822, d343431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341822, d343431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93267 (p : Pattern) (ha : d341828 p = 1) (hb : d343437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341819 q = 1) (hb : d343428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341819, d343428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93265 q ha hb
    | true =>
      simp only [d341819, d343428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93246 q ha hb
  have h2 (q : Pattern) (ha : d341820 q = 1) (hb : d343429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341820, d343429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341820, d343429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341821 q = 1) (hb : d343430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341821, d343430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341821, d343430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341823 q = 1) (hb : d343432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341823, d343432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93246 q ha hb
    | true =>
      simp only [d341823, d343432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93266 q ha hb
  have h5 (q : Pattern) (ha : d341824 q = 1) (hb : d343433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341824, d343433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341824, d343433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341825 q = 1) (hb : d343434 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341825, d343434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341825, d343434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341826 q = 1) (hb : d343435 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341826, d343435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341826, d343435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341729 q = 1) (hb : d343338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341729, d343338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93246 q ha hb
    | true =>
      simp only [d341729, d343338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93247 q ha hb
  have h9 (q : Pattern) (ha : d341730 q = 1) (hb : d343339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341730, d343339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341730, d343339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341731 q = 1) (hb : d343340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341731, d343340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341731, d343340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341733 q = 1) (hb : d343342 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341733, d343342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93247 q ha hb
    | true =>
      simp only [d341733, d343342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93248 q ha hb
  have h12 (q : Pattern) (ha : d341734 q = 1) (hb : d343343 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341734, d343343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341734, d343343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d341735 q = 1) (hb : d343344 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341735, d343344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341735, d343344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341736 q = 1) (hb : d343345 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341736, d343345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341736, d343345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d341827 q = 1) (hb : d343436 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d341827, d343436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341827, d343436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d341828 q = 1) (hb : d343437 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d341828, d343437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341828, d343437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro93268 (p : Pattern) (ha : d341834 p = 1) (hb : d343443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341829 q = 1) (hb : d343438 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341829, d343438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93267 q ha hb
    | true =>
      simp only [d341829, d343438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341830 q = 1) (hb : d343439 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341830, d343439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341830, d343439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341831 q = 1) (hb : d343440 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341831, d343440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341831, d343440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341832 q = 1) (hb : d343441 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341832, d343441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341832, d343441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341833 q = 1) (hb : d343442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341833, d343442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341833, d343442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341834 q = 1) (hb : d343443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341834, d343443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341834, d343443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93269 (p : Pattern) (ha : d341840 p = 1) (hb : d343449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341837 q = 1) (hb : d343446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341837, d343446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341837, d343446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341838 q = 1) (hb : d343447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341838, d343447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341838, d343447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341839 q = 1) (hb : d343448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341839, d343448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341839, d343448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341840 q = 1) (hb : d343449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341840, d343449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341840, d343449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93270 (p : Pattern) (ha : d341846 p = 1) (hb : d343455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341777 q = 1) (hb : d343386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341777, d343386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93257 q ha hb
    | true =>
      simp only [d341777, d343386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93258 q ha hb
  have h2 (q : Pattern) (ha : d341778 q = 1) (hb : d343387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341778, d343387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341778, d343387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341779 q = 1) (hb : d343388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341779, d343388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341779, d343388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341780 q = 1) (hb : d343389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341780, d343389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341780, d343389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341787 q = 1) (hb : d343396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341787, d343396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93259 q ha hb
    | true =>
      simp only [d341787, d343396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93260 q ha hb
  have h6 (q : Pattern) (ha : d341788 q = 1) (hb : d343397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341788, d343397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341788, d343397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341789 q = 1) (hb : d343398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341789, d343398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341789, d343398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341835 q = 1) (hb : d343444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341835, d343444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93268 q ha hb
    | true =>
      simp only [d341835, d343444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d341754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d341836 q = 1) (hb : d343445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341836, d343445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341836, d343445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d341841 q = 1) (hb : d343450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341841, d343450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93269 q ha hb
    | true =>
      simp only [d341841, d343450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d341842 q = 1) (hb : d343451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341842, d343451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341842, d343451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341843 q = 1) (hb : d343452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341843, d343452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341843, d343452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341844 q = 1) (hb : d343453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341844, d343453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341844, d343453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d341845 q = 1) (hb : d343454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341845, d343454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341845, d343454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d341846 q = 1) (hb : d343455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341846, d343455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341846, d343455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro93271 (p : Pattern) (ha : d341847 p = 1) (hb : d343456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341746 q = 1) (hb : d343355 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341747 q = 1) (hb : d343356 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341747, d343356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341773 q = 1) (hb : d343382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341773, d343382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341773, d343382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341847 q = 1) (hb : d343456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341847, d343456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341847, d343456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93272 (p : Pattern) (ha : d341848 p = 1) (hb : d343457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341750 q = 1) (hb : d343359 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341751 q = 1) (hb : d343360 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341751, d343360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341775 q = 1) (hb : d343384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341775, d343384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341775, d343384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341848 q = 1) (hb : d343457 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341848, d343457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341848, d343457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93273 (p : Pattern) (ha : d341853 p = 1) (hb : d343462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341746 q = 1) (hb : d343355 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341746, d343355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341781 q = 1) (hb : d343390 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341781, d343390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341781, d343390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341782 q = 1) (hb : d343391 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341782, d343391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341782, d343391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341853 q = 1) (hb : d343462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341853, d343462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341853, d343462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93274 (p : Pattern) (ha : d341854 p = 1) (hb : d343463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341744 q = 1) (hb : d343353 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93250 q ha hb
    | true =>
      simp only [d341744, d343353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341745 q = 1) (hb : d343354 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341745, d343354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341750 q = 1) (hb : d343359 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341750, d343359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341784 q = 1) (hb : d343393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341784, d343393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341784, d343393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341785 q = 1) (hb : d343394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341785, d343394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341785, d343394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341854 q = 1) (hb : d343463 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341854, d343463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341854, d343463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93275 (p : Pattern) (ha : d341858 p = 1) (hb : d343467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341829 q = 1) (hb : d343438 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341829, d343438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93267 q ha hb
    | true =>
      simp only [d341829, d343438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341830 q = 1) (hb : d343439 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341830, d343439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341830, d343439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341831 q = 1) (hb : d343440 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341831, d343440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341831, d343440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341832 q = 1) (hb : d343441 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341832, d343441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341832, d343441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341833 q = 1) (hb : d343442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341833, d343442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341833, d343442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341858 q = 1) (hb : d343467 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341858, d343467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341858, d343467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93276 (p : Pattern) (ha : d341861 p = 1) (hb : d343470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341740 q = 1) (hb : d343349 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93249 q ha hb
    | true =>
      simp only [d341740, d343349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341741 q = 1) (hb : d343350 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341741, d343350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341837 q = 1) (hb : d343446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341837, d343446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341837, d343446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341838 q = 1) (hb : d343447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341838, d343447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341838, d343447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341839 q = 1) (hb : d343448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341839, d343448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341839, d343448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341861 q = 1) (hb : d343470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341861, d343470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341861, d343470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93277 (p : Pattern) (ha : d341867 p = 1) (hb : d343476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341777 q = 1) (hb : d343386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341777, d343386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93257 q ha hb
    | true =>
      simp only [d341777, d343386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93258 q ha hb
  have h2 (q : Pattern) (ha : d341778 q = 1) (hb : d343387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341778, d343387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341778, d343387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341779 q = 1) (hb : d343388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341779, d343388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341779, d343388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341780 q = 1) (hb : d343389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341780, d343389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341780, d343389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341787 q = 1) (hb : d343396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341787, d343396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93259 q ha hb
    | true =>
      simp only [d341787, d343396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93260 q ha hb
  have h6 (q : Pattern) (ha : d341788 q = 1) (hb : d343397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341788, d343397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341788, d343397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341789 q = 1) (hb : d343398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341789, d343398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341789, d343398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341835 q = 1) (hb : d343444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341835, d343444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93268 q ha hb
    | true =>
      simp only [d341835, d343444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d341754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d341836 q = 1) (hb : d343445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341836, d343445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341836, d343445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d341841 q = 1) (hb : d343450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341841, d343450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93269 q ha hb
    | true =>
      simp only [d341841, d343450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d341842 q = 1) (hb : d343451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341842, d343451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341842, d343451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341843 q = 1) (hb : d343452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341843, d343452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341843, d343452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341844 q = 1) (hb : d343453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341844, d343453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341844, d343453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d341845 q = 1) (hb : d343454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341845, d343454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341845, d343454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d341849 q = 1) (hb : d343458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341849, d343458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93271 q ha hb
    | true =>
      simp only [d341849, d343458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93272 q ha hb
  have h17 (q : Pattern) (ha : d341850 q = 1) (hb : d343459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341850, d343459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341850, d343459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d341851 q = 1) (hb : d343460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341851, d343460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d341851, d343460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d341852 q = 1) (hb : d343461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341852, d343461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341852, d343461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d341855 q = 1) (hb : d343464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341855, d343464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93273 q ha hb
    | true =>
      simp only [d341855, d343464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93274 q ha hb
  have h21 (q : Pattern) (ha : d341856 q = 1) (hb : d343465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341856, d343465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341856, d343465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d341857 q = 1) (hb : d343466 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341857, d343466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d341857, d343466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d341859 q = 1) (hb : d343468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341859, d343468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93275 q ha hb
    | true =>
      simp only [d341859, d343468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93254 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d341764 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d341860 q = 1) (hb : d343469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341860, d343469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d341860, d343469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d341862 q = 1) (hb : d343471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341862, d343471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93276 q ha hb
    | true =>
      simp only [d341862, d343471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d341863 q = 1) (hb : d343472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341863, d343472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d341863, d343472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d341864 q = 1) (hb : d343473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341864, d343473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d341864, d343473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d341865 q = 1) (hb : d343474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341865, d343474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d341865, d343474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d341866 q = 1) (hb : d343475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341866, d343475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d341866, d343475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d341867 q = 1) (hb : d343476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341867, d343476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341867, d343476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro93278 (p : Pattern) (ha : d341874 p = 1) (hb : d343483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341754 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
    | true =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
  have h2 (q : Pattern) (ha : d341755 q = 1) (hb : d343364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341755, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341755, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341756 q = 1) (hb : d343365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341756, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341756, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341757 q = 1) (hb : d343366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341757, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341757, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341758 q = 1) (hb : d343367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341758, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341758, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341869 q = 1) (hb : d343478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341869, d343478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
    | true =>
      simp only [d341869, d343478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341870 q = 1) (hb : d343479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341870, d343479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341870, d343479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341871 q = 1) (hb : d343480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341871, d343480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341871, d343480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341872 q = 1) (hb : d343481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341872, d343481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341872, d343481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341873 q = 1) (hb : d343482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341873, d343482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341873, d343482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341874 q = 1) (hb : d343483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341874, d343483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341874, d343483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93279 (p : Pattern) (ha : d341880 p = 1) (hb : d343489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341869 q = 1) (hb : d343478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341869, d343478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
    | true =>
      simp only [d341869, d343478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341870 q = 1) (hb : d343479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341870, d343479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341870, d343479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341871 q = 1) (hb : d343480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341871, d343480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341871, d343480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341872 q = 1) (hb : d343481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341872, d343481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341872, d343481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341873 q = 1) (hb : d343482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341873, d343482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341873, d343482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341875 q = 1) (hb : d343484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341875, d343484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93255 q ha hb
    | true =>
      simp only [d341875, d343484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341876 q = 1) (hb : d343485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341876, d343485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341876, d343485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341877 q = 1) (hb : d343486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341877, d343486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341877, d343486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341878 q = 1) (hb : d343487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341878, d343487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341878, d343487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341879 q = 1) (hb : d343488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341879, d343488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341879, d343488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341880 q = 1) (hb : d343489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341880, d343489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341880, d343489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93280 (p : Pattern) (ha : d341887 p = 1) (hb : d343496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341859 q = 1) (hb : d343468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341859, d343468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93275 q ha hb
    | true =>
      simp only [d341859, d343468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93254 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341860 q = 1) (hb : d343469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341860, d343469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341860, d343469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d341862 q = 1) (hb : d343471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341862, d343471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93276 q ha hb
    | true =>
      simp only [d341862, d343471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341863 q = 1) (hb : d343472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341863, d343472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341863, d343472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341864 q = 1) (hb : d343473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341864, d343473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341864, d343473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341885 q = 1) (hb : d343494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341885, d343494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341885, d343494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341886 q = 1) (hb : d343495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341886, d343495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341886, d343495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341887 q = 1) (hb : d343496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341887, d343496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341887, d343496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro93281 (p : Pattern) (ha : d341889 p = 1) (hb : d343498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341875 q = 1) (hb : d343484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341875, d343484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93255 q ha hb
    | true =>
      simp only [d341875, d343484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341876 q = 1) (hb : d343485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341876, d343485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341876, d343485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341877 q = 1) (hb : d343486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341877, d343486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341877, d343486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341878 q = 1) (hb : d343487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341878, d343487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341878, d343487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341879 q = 1) (hb : d343488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341879, d343488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341879, d343488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341889 q = 1) (hb : d343498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341889, d343498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341889, d343498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93282 (p : Pattern) (ha : d341909 p = 1) (hb : d343518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341895 q = 1) (hb : d343504 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341895, d343504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341895, d343504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93262 q ha hb
  have h2 (q : Pattern) (ha : d341800 q = 1) (hb : d343409 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341800, d343409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93262 q ha hb
    | true =>
      simp only [d341800, d343409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341896 q = 1) (hb : d343505 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341896, d343505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341896, d343505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341801 q = 1) (hb : d343410 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341801, d343410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341801, d343410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341897 q = 1) (hb : d343506 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341897, d343506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341897, d343506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341898 q = 1) (hb : d343507 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341898, d343507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341898, d343507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341899 q = 1) (hb : d343508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341899, d343508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341899, d343508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93263 q ha hb
  have h8 (q : Pattern) (ha : d341805 q = 1) (hb : d343414 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341805, d343414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93263 q ha hb
    | true =>
      simp only [d341805, d343414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341900 q = 1) (hb : d343509 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341900, d343509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341900, d343509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341806 q = 1) (hb : d343415 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341806, d343415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341806, d343415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d341901 q = 1) (hb : d343510 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341901, d343510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341901, d343510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341902 q = 1) (hb : d343511 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341902, d343511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341902, d343511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341903 q = 1) (hb : d343512 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341903, d343512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341903, d343512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341904 q = 1) (hb : d343513 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341904, d343513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341904, d343513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93264 q ha hb
  have h15 (q : Pattern) (ha : d341813 q = 1) (hb : d343422 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341813, d343422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93264 q ha hb
    | true =>
      simp only [d341813, d343422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d341905 q = 1) (hb : d343514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341905, d343514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341905, d343514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341814 q = 1) (hb : d343423 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341814, d343423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341814, d343423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d341906 q = 1) (hb : d343515 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341906, d343515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341906, d343515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d341907 q = 1) (hb : d343516 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341907, d343516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d341907, d343516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d341646 q = 1) (hb : d343256 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341646, d343256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341646, d343256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
  have h21 (q : Pattern) (ha : d341555 q = 1) (hb : d343165 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
    | true =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d341647 q = 1) (hb : d343257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341647, d343257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d341647, d343257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d341556 q = 1) (hb : d343166 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d341648 q = 1) (hb : d343258 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341648, d343258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d341648, d343258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d341649 q = 1) (hb : d343259 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341649, d343259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d341649, d343259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d341908 q = 1) (hb : d343517 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341908, d343517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d341908, d343517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d341909 q = 1) (hb : d343518 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341909, d343518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341909, d343518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro93283 (p : Pattern) (ha : d341915 p = 1) (hb : d343524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341637 q = 1) (hb : d343247 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341637, d343247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341637, d343247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93212 q ha hb
  have h2 (q : Pattern) (ha : d341542 q = 1) (hb : d343152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341542, d343152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93212 q ha hb
    | true =>
      simp only [d341542, d343152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341638 q = 1) (hb : d343248 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341638, d343248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341638, d343248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341543 q = 1) (hb : d343153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341543, d343153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341543, d343153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341639 q = 1) (hb : d343249 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341639, d343249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341639, d343249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341640 q = 1) (hb : d343250 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341640, d343250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341640, d343250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341641 q = 1) (hb : d343251 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341641, d343251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341641, d343251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93213 q ha hb
  have h8 (q : Pattern) (ha : d341547 q = 1) (hb : d343157 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341547, d343157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93213 q ha hb
    | true =>
      simp only [d341547, d343157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341642 q = 1) (hb : d343252 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341642, d343252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341642, d343252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341548 q = 1) (hb : d343158 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341548, d343158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341548, d343158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d341643 q = 1) (hb : d343253 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341643, d343253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341643, d343253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341644 q = 1) (hb : d343254 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341644, d343254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341644, d343254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341645 q = 1) (hb : d343255 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341645, d343255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341645, d343255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341646 q = 1) (hb : d343256 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341646, d343256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341646, d343256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
  have h15 (q : Pattern) (ha : d341555 q = 1) (hb : d343165 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
    | true =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d341647 q = 1) (hb : d343257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341647, d343257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341647, d343257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341556 q = 1) (hb : d343166 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d341648 q = 1) (hb : d343258 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341648, d343258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341648, d343258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d341649 q = 1) (hb : d343259 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341649, d343259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d341649, d343259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d341910 q = 1) (hb : d343519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
  have h21 (q : Pattern) (ha : d341720 q = 1) (hb : d343329 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
    | true =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d341911 q = 1) (hb : d343520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d341721 q = 1) (hb : d343330 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d341912 q = 1) (hb : d343521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d341913 q = 1) (hb : d343522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d341914 q = 1) (hb : d343523 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341914, d343523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d341914, d343523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d341915 q = 1) (hb : d343524 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341915, d343524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341915, d343524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro93284 (p : Pattern) (ha : d341920 p = 1) (hb : d343529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341646 q = 1) (hb : d343256 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341646, d343256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341646, d343256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
  have h2 (q : Pattern) (ha : d341555 q = 1) (hb : d343165 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93214 q ha hb
    | true =>
      simp only [d341555, d343165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341647 q = 1) (hb : d343257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341647, d343257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341647, d343257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341556 q = 1) (hb : d343166 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341556, d343166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341648 q = 1) (hb : d343258 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341648, d343258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341648, d343258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341649 q = 1) (hb : d343259 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341649, d343259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341649, d343259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341910 q = 1) (hb : d343519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
  have h8 (q : Pattern) (ha : d341720 q = 1) (hb : d343329 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
    | true =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341911 q = 1) (hb : d343520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341721 q = 1) (hb : d343330 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d341912 q = 1) (hb : d343521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341913 q = 1) (hb : d343522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341914 q = 1) (hb : d343523 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341914, d343523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341914, d343523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341919 q = 1) (hb : d343528 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341919, d343528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341919, d343528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d341920 q = 1) (hb : d343529 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341920, d343529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341920, d343529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93285 (p : Pattern) (ha : d341926 p = 1) (hb : d343535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341414 q = 1) (hb : d343027 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341414, d343027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341414, d343027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93174 q ha hb
  have h2 (q : Pattern) (ha : d341341 q = 1) (hb : d342954 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341341, d342954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93174 q ha hb
    | true =>
      simp only [d341341, d342954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341415 q = 1) (hb : d343028 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341415, d343028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341415, d343028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341342 q = 1) (hb : d342955 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341342, d342955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341342, d342955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341416 q = 1) (hb : d343029 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341416, d343029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341416, d343029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341417 q = 1) (hb : d343030 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341417, d343030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341417, d343030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341910 q = 1) (hb : d343519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
  have h8 (q : Pattern) (ha : d341720 q = 1) (hb : d343329 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
    | true =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341911 q = 1) (hb : d343520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341721 q = 1) (hb : d343330 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d341912 q = 1) (hb : d343521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341913 q = 1) (hb : d343522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341925 q = 1) (hb : d343534 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341925, d343534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341925, d343534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341919 q = 1) (hb : d343528 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341919, d343528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341919, d343528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d341926 q = 1) (hb : d343535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341926, d343535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341926, d343535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93286 (p : Pattern) (ha : d341930 p = 1) (hb : d343539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341910 q = 1) (hb : d343519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341910, d343519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
  have h2 (q : Pattern) (ha : d341720 q = 1) (hb : d343329 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93245 q ha hb
    | true =>
      simp only [d341720, d343329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341911 q = 1) (hb : d343520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341911, d343520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341721 q = 1) (hb : d343330 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341721, d343330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341912 q = 1) (hb : d343521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341912, d343521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341913 q = 1) (hb : d343522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341913, d343522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341919 q = 1) (hb : d343528 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d341919, d343528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341919, d343528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341930 q = 1) (hb : d343539 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d341930, d343539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341930, d343539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93287 (p : Pattern) (ha : d341936 p = 1) (hb : d343545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341916 q = 1) (hb : d343525 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341916, d343525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93282 q ha hb
    | true =>
      simp only [d341916, d343525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93283 q ha hb
  have h2 (q : Pattern) (ha : d341917 q = 1) (hb : d343526 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341917, d343526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341917, d343526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341918 q = 1) (hb : d343527 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341918, d343527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341918, d343527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341921 q = 1) (hb : d343530 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341921, d343530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93283 q ha hb
    | true =>
      simp only [d341921, d343530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93284 q ha hb
  have h5 (q : Pattern) (ha : d341922 q = 1) (hb : d343531 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341922, d343531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341922, d343531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341923 q = 1) (hb : d343532 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341923, d343532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341923, d343532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341924 q = 1) (hb : d343533 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341924, d343533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341924, d343533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341927 q = 1) (hb : d343536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341927, d343536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93283 q ha hb
    | true =>
      simp only [d341927, d343536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93285 q ha hb
  have h9 (q : Pattern) (ha : d341928 q = 1) (hb : d343537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341928, d343537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341928, d343537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341929 q = 1) (hb : d343538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341929, d343538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341929, d343538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341931 q = 1) (hb : d343540 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341931, d343540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93285 q ha hb
    | true =>
      simp only [d341931, d343540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93286 q ha hb
  have h12 (q : Pattern) (ha : d341932 q = 1) (hb : d343541 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341932, d343541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341932, d343541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d341933 q = 1) (hb : d343542 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341933, d343542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341933, d343542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341934 q = 1) (hb : d343543 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341934, d343543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341934, d343543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d341935 q = 1) (hb : d343544 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d341935, d343544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341935, d343544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d341936 q = 1) (hb : d343545 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d341936, d343545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341936, d343545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro93288 (p : Pattern) (ha : d341941 p = 1) (hb : d343550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341927 q = 1) (hb : d343536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341927, d343536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93283 q ha hb
    | true =>
      simp only [d341927, d343536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93285 q ha hb
  have h2 (q : Pattern) (ha : d341928 q = 1) (hb : d343537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341928, d343537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341928, d343537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341929 q = 1) (hb : d343538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341929, d343538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341929, d343538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341931 q = 1) (hb : d343540 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341931, d343540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93285 q ha hb
    | true =>
      simp only [d341931, d343540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93286 q ha hb
  have h5 (q : Pattern) (ha : d341932 q = 1) (hb : d343541 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341932, d343541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341932, d343541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341933 q = 1) (hb : d343542 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341933, d343542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341933, d343542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341934 q = 1) (hb : d343543 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341934, d343543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341934, d343543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341939 q = 1) (hb : d343548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341939, d343548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341939, d343548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341940 q = 1) (hb : d343549 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d341940, d343549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341940, d343549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341941 q = 1) (hb : d343550 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d341941, d343550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341941, d343550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro93289 (p : Pattern) (ha : d341947 p = 1) (hb : d343556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341937 q = 1) (hb : d343546 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341937, d343546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93287 q ha hb
    | true =>
      simp only [d341937, d343546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341938 q = 1) (hb : d343547 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341938, d343547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341938, d343547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341942 q = 1) (hb : d343551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341942, d343551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93288 q ha hb
    | true =>
      simp only [d341942, d343551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341943 q = 1) (hb : d343552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341943, d343552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341943, d343552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341944 q = 1) (hb : d343553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341944, d343553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341944, d343553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341945 q = 1) (hb : d343554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341945, d343554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341945, d343554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341946 q = 1) (hb : d343555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341946, d343555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341946, d343555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341947 q = 1) (hb : d343556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341947, d343556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341947, d343556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93290 (p : Pattern) (ha : d341949 p = 1) (hb : d343558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341931 q = 1) (hb : d343540 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341931, d343540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93285 q ha hb
    | true =>
      simp only [d341931, d343540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93286 q ha hb
  have h2 (q : Pattern) (ha : d341932 q = 1) (hb : d343541 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341932, d343541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341932, d343541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341933 q = 1) (hb : d343542 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341933, d343542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341933, d343542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341939 q = 1) (hb : d343548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341939, d343548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341939, d343548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341948 q = 1) (hb : d343557 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d341948, d343557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341948, d343557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341949 q = 1) (hb : d343558 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d341949, d343558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341949, d343558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93291 (p : Pattern) (ha : d341955 p = 1) (hb : d343564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341942 q = 1) (hb : d343551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341942, d343551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93288 q ha hb
    | true =>
      simp only [d341942, d343551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341943 q = 1) (hb : d343552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341943, d343552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341943, d343552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341950 q = 1) (hb : d343559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341950, d343559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93290 q ha hb
    | true =>
      simp only [d341950, d343559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341951 q = 1) (hb : d343560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341951, d343560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341951, d343560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341952 q = 1) (hb : d343561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341952, d343561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341952, d343561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341953 q = 1) (hb : d343562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341953, d343562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341953, d343562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341954 q = 1) (hb : d343563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341954, d343563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341954, d343563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341955 q = 1) (hb : d343564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341955, d343564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341955, d343564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93292 (p : Pattern) (ha : d341966 p = 1) (hb : d343570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341942 q = 1) (hb : d343551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341942, d343551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93288 q ha hb
    | true =>
      simp only [d341942, d343551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341943 q = 1) (hb : d343552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341943, d343552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341943, d343552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341963 q = 1) (hb : d343567 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341963, d343567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341963, d343567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341964 q = 1) (hb : d343568 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341964, d343568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341964, d343568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341965 q = 1) (hb : d343569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341965, d343569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341965, d343569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341966 q = 1) (hb : d343570 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341966, d343570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341966, d343570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93293 (p : Pattern) (ha : d341972 p = 1) (hb : d343576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341956 q = 1) (hb : d343565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341956, d343565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93289 q ha hb
    | true =>
      simp only [d341956, d343565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93291 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341961 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341962 q = 1) (hb : d343566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341962, d343566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341962, d343566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d341967 q = 1) (hb : d343571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341967, d343571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93292 q ha hb
    | true =>
      simp only [d341967, d343571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341968 q = 1) (hb : d343572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341968, d343572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341968, d343572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341969 q = 1) (hb : d343573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341969, d343573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341969, d343573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341970 q = 1) (hb : d343574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341970, d343574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341970, d343574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341971 q = 1) (hb : d343575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341971, d343575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341971, d343575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341972 q = 1) (hb : d343576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341972, d343576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341972, d343576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro93294 (p : Pattern) (ha : d341960 p = 1) (hb : d343581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341950 q = 1) (hb : d343559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341950, d343559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93290 q ha hb
    | true =>
      simp only [d341950, d343559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341951 q = 1) (hb : d343560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341951, d343560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341951, d343560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341957 q = 1) (hb : d343578 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d341957, d343578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341957, d343578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341958 q = 1) (hb : d343579 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d341958, d343579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341958, d343579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341959 q = 1) (hb : d343580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d341959, d343580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341959, d343580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341960 q = 1) (hb : d343581 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d341960, d343581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341960, d343581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93295 (p : Pattern) (ha : d341979 p = 1) (hb : d343587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341974 q = 1) (hb : d343582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341974, d343582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93294 q ha hb
    | true =>
      simp only [d341974, d343582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341975 q = 1) (hb : d343583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341975, d343583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341975, d343583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341976 q = 1) (hb : d343584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341976, d343584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341976, d343584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341977 q = 1) (hb : d343585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341977, d343585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341977, d343585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341978 q = 1) (hb : d343586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341978, d343586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341978, d343586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341979 q = 1) (hb : d343587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341979, d343587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341979, d343587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93296 (p : Pattern) (ha : d341985 p = 1) (hb : d343593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341760 q = 1) (hb : d343369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341760, d343369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341760, d343369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93253 q ha hb
  have h2 (q : Pattern) (ha : d341761 q = 1) (hb : d343370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341761, d343370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341761, d343370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341770 q = 1) (hb : d343379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341770, d343379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93253 q ha hb
    | true =>
      simp only [d341770, d343379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93256 q ha hb
  have h4 (q : Pattern) (ha : d341771 q = 1) (hb : d343380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341771, d343380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341771, d343380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341772 q = 1) (hb : d343381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341772, d343381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341772, d343381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341868 q = 1) (hb : d343477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341868, d343477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93270 q ha hb
    | true =>
      simp only [d341868, d343477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93277 q ha hb
  have h7 (q : Pattern) (ha : d341881 q = 1) (hb : d343490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341881, d343490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93278 q ha hb
    | true =>
      simp only [d341881, d343490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93279 q ha hb
  have h8 (q : Pattern) (ha : d341882 q = 1) (hb : d343491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341882, d343491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341882, d343491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341883 q = 1) (hb : d343492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341883, d343492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341883, d343492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d341884 q = 1) (hb : d343493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341884, d343493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341884, d343493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341888 q = 1) (hb : d343497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341888, d343497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341888, d343497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93280 q ha hb
  have h12 (q : Pattern) (ha : d341890 q = 1) (hb : d343499 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341890, d343499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341890, d343499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93281 q ha hb
  have h13 (q : Pattern) (ha : d341891 q = 1) (hb : d343500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341891, d343500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341891, d343500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d341892 q = 1) (hb : d343501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341892, d343501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341892, d343501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d341893 q = 1) (hb : d343502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341893, d343502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341893, d343502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d341894 q = 1) (hb : d343503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341894, d343503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341894, d343503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341973 q = 1) (hb : d343577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341973, d343577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341973, d343577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93293 q ha hb
  have h18 (q : Pattern) (ha : d341980 q = 1) (hb : d343588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341980, d343588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341980, d343588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93295 q ha hb
  have h19 (q : Pattern) (ha : d341981 q = 1) (hb : d343589 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341981, d343589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d341981, d343589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d341982 q = 1) (hb : d343590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341982, d343590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d341982, d343590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d341983 q = 1) (hb : d343591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341983, d343591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d341983, d343591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d341984 q = 1) (hb : d343592 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341984, d343592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d341984, d343592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d341985 q = 1) (hb : d343593 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d341985, d343593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341985, d343593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro93297 (p : Pattern) (ha : d341991 p = 1) (hb : d343599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341986 q = 1) (hb : d343594 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d341986, d343594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341986, d343594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93296 q ha hb
  have h2 (q : Pattern) (ha : d341987 q = 1) (hb : d343595 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d341987, d343595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341987, d343595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341988 q = 1) (hb : d343596 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d341988, d343596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341988, d343596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341989 q = 1) (hb : d343597 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d341989, d343597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341989, d343597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341990 q = 1) (hb : d343598 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d341990, d343598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341990, d343598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341991 q = 1) (hb : d343599 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d341991, d343599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341991, d343599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93298 (p : Pattern) (ha : d341995 p = 1) (hb : d343603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2001 q = 1) (hb : d341328 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d341328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d341328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341521 q = 1) (hb : d343134 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d341521, d343134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341521, d343134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2005 q = 1) (hb : d341526 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d341526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d2005, d341526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d341527 q = 1) (hb : d343139 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d341527, d343139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d341527, d343139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d341995 q = 1) (hb : d343603 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d341995, d343603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341995, d343603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro93299 (p : Pattern) (ha : d342001 p = 1) (hb : d343609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2001 q = 1) (hb : d341328 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d341328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d341328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2005 q = 1) (hb : d341526 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d341526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d2005, d341526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d341527 q = 1) (hb : d343139 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d341527, d343139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d341527, d343139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2006 q = 1) (hb : d341531 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d341531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2006, d341531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d342001 q = 1) (hb : d343609 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d342001, d343609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342001, d343609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro93300 (p : Pattern) (ha : d342007 p = 1) (hb : d343615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341791 q = 1) (hb : d343400 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93261 q ha hb
    | true =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341792 q = 1) (hb : d343401 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341996 q = 1) (hb : d343604 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93298 q ha hb
    | true =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341997 q = 1) (hb : d343605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341998 q = 1) (hb : d343606 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341998, d343606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341998, d343606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341999 q = 1) (hb : d343607 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341999, d343607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341999, d343607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342000 q = 1) (hb : d343608 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342000, d343608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342000, d343608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342002 q = 1) (hb : d343610 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93299 q ha hb
    | true =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342003 q = 1) (hb : d343611 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d342004 q = 1) (hb : d343612 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d341796 q = 1) (hb : d343405 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341796, d343405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341796, d343405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342005 q = 1) (hb : d343613 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342005, d343613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342005, d343613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d342006 q = 1) (hb : d343614 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342006, d343614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d342006, d343614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d342007 q = 1) (hb : d343615 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342007, d343615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342007, d343615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro93301 (p : Pattern) (ha : d342017 p = 1) (hb : d343625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341996 q = 1) (hb : d343604 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93298 q ha hb
    | true =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341997 q = 1) (hb : d343605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342002 q = 1) (hb : d343610 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93299 q ha hb
    | true =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342003 q = 1) (hb : d343611 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342004 q = 1) (hb : d343612 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341529 q = 1) (hb : d343141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341529, d343141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93211 q ha hb
    | true =>
      simp only [d341529, d343141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341530 q = 1) (hb : d343142 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341530, d343142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341530, d343142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d341535 q = 1) (hb : d343145 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341535, d343145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341535, d343145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342012 q = 1) (hb : d343620 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342012, d343620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342012, d343620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d342013 q = 1) (hb : d343621 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342013, d343621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342013, d343621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342014 q = 1) (hb : d343622 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d342015 q = 1) (hb : d343623 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342015, d343623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342015, d343623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d342016 q = 1) (hb : d343624 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342016, d343624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d342016, d343624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d342017 q = 1) (hb : d343625 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342017, d343625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342017, d343625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro93302 (p : Pattern) (ha : d342025 p = 1) (hb : d343633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341996 q = 1) (hb : d343604 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93298 q ha hb
    | true =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341997 q = 1) (hb : d343605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342002 q = 1) (hb : d343610 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93299 q ha hb
    | true =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342003 q = 1) (hb : d343611 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342004 q = 1) (hb : d343612 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342023 q = 1) (hb : d343631 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342023, d343631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342023, d343631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342024 q = 1) (hb : d343632 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342024, d343632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342024, d343632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d342014 q = 1) (hb : d343622 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342015 q = 1) (hb : d343623 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342015, d343623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342015, d343623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d342016 q = 1) (hb : d343624 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342016, d343624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342016, d343624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342025 q = 1) (hb : d343633 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342025, d343633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342025, d343633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro93303 (p : Pattern) (ha : d342033 p = 1) (hb : d343641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342002 q = 1) (hb : d343610 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93299 q ha hb
    | true =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342003 q = 1) (hb : d343611 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342014 q = 1) (hb : d343622 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342030 q = 1) (hb : d343638 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342030, d343638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342030, d343638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342031 q = 1) (hb : d343639 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342031, d343639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342031, d343639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342032 q = 1) (hb : d343640 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342032, d343640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342032, d343640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342033 q = 1) (hb : d343641 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342033, d343641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342033, d343641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro93304 (p : Pattern) (ha : d342039 p = 1) (hb : d343647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342008 q = 1) (hb : d343616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342008, d343616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93300 q ha hb
    | true =>
      simp only [d342008, d343616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342009 q = 1) (hb : d343617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342009, d343617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342009, d343617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342010 q = 1) (hb : d343618 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342010, d343618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342010, d343618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342011 q = 1) (hb : d343619 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342011, d343619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342011, d343619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342018 q = 1) (hb : d343626 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342018, d343626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93301 q ha hb
    | true =>
      simp only [d342018, d343626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342019 q = 1) (hb : d343627 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342019, d343627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342019, d343627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342020 q = 1) (hb : d343628 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342020, d343628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342020, d343628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342021 q = 1) (hb : d343629 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342021, d343629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342021, d343629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342022 q = 1) (hb : d343630 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342022, d343630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342022, d343630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342026 q = 1) (hb : d343634 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
    | true =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342027 q = 1) (hb : d343635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d342028 q = 1) (hb : d343636 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342028, d343636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342028, d343636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d342029 q = 1) (hb : d343637 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342029, d343637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342029, d343637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d342036 q = 1) (hb : d343644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342037 q = 1) (hb : d343645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d342038 q = 1) (hb : d343646 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342038, d343646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342038, d343646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d342039 q = 1) (hb : d343647 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342039, d343647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342039, d343647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93305 (p : Pattern) (ha : d342040 p = 1) (hb : d343648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341996 q = 1) (hb : d343604 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93298 q ha hb
    | true =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341997 q = 1) (hb : d343605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342002 q = 1) (hb : d343610 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93299 q ha hb
    | true =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342003 q = 1) (hb : d343611 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342004 q = 1) (hb : d343612 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341529 q = 1) (hb : d343141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341529, d343141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93211 q ha hb
    | true =>
      simp only [d341529, d343141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341530 q = 1) (hb : d343142 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341530, d343142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341530, d343142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341533 q = 1) (hb : d343143 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93209 q hb ha
    | true =>
      simp only [d341533, d343143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d341534 q = 1) (hb : d343144 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341534, d343144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d341535 q = 1) (hb : d343145 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341535, d343145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341535, d343145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342012 q = 1) (hb : d343620 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342012, d343620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342012, d343620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d342013 q = 1) (hb : d343621 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342013, d343621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342013, d343621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342014 q = 1) (hb : d343622 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342014, d343622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d342030 q = 1) (hb : d343638 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342030, d343638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342030, d343638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d342031 q = 1) (hb : d343639 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342031, d343639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342031, d343639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342032 q = 1) (hb : d343640 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342032, d343640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342032, d343640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d342040 q = 1) (hb : d343648 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342040, d343648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342040, d343648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro93306 (p : Pattern) (ha : d342047 p = 1) (hb : d343655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342041 q = 1) (hb : d343649 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342041, d343649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93305 q ha hb
    | true =>
      simp only [d342041, d343649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342042 q = 1) (hb : d343650 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342042, d343650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342042, d343650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342043 q = 1) (hb : d343651 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342043, d343651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342043, d343651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342044 q = 1) (hb : d343652 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342044, d343652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342044, d343652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342036 q = 1) (hb : d343644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342037 q = 1) (hb : d343645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342045 q = 1) (hb : d343653 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342045, d343653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342045, d343653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342046 q = 1) (hb : d343654 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342046, d343654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342046, d343654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342047 q = 1) (hb : d343655 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342047, d343655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342047, d343655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93307 (p : Pattern) (ha : d342051 p = 1) (hb : d343659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342036 q = 1) (hb : d343644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342037 q = 1) (hb : d343645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342046 q = 1) (hb : d343654 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342046, d343654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342046, d343654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342051 q = 1) (hb : d343659 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342051, d343659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342051, d343659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93308 (p : Pattern) (ha : d342058 p = 1) (hb : d343666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342048 q = 1) (hb : d343656 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342048, d343656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93304 q ha hb
    | true =>
      simp only [d342048, d343656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93306 q ha hb
  have h2 (q : Pattern) (ha : d342049 q = 1) (hb : d343657 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342049, d343657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342049, d343657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342050 q = 1) (hb : d343658 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342050, d343658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342050, d343658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342052 q = 1) (hb : d343660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342052, d343660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93306 q ha hb
    | true =>
      simp only [d342052, d343660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93307 q ha hb
  have h5 (q : Pattern) (ha : d342053 q = 1) (hb : d343661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342053, d343661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342053, d343661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342054 q = 1) (hb : d343662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342054, d343662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342054, d343662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342055 q = 1) (hb : d343663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342055, d343663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342055, d343663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342056 q = 1) (hb : d343664 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342056, d343664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342056, d343664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342057 q = 1) (hb : d343665 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d342057, d343665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342057, d343665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342058 q = 1) (hb : d343666 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d342058, d343666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342058, d343666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro93309 (p : Pattern) (ha : d342062 p = 1) (hb : d343670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342052 q = 1) (hb : d343660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342052, d343660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93306 q ha hb
    | true =>
      simp only [d342052, d343660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93307 q ha hb
  have h2 (q : Pattern) (ha : d342053 q = 1) (hb : d343661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342053, d343661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342053, d343661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342054 q = 1) (hb : d343662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342054, d343662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342054, d343662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342056 q = 1) (hb : d343664 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342056, d343664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342056, d343664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342061 q = 1) (hb : d343669 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d342061, d343669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342061, d343669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342062 q = 1) (hb : d343670 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d342062, d343670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342062, d343670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93310 (p : Pattern) (ha : d342068 p = 1) (hb : d343676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342065 q = 1) (hb : d343673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342066 q = 1) (hb : d343674 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342067 q = 1) (hb : d343675 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342067, d343675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342067, d343675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342068 q = 1) (hb : d343676 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342068, d343676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342068, d343676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93311 (p : Pattern) (ha : d342072 p = 1) (hb : d343680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342069 q = 1) (hb : d343677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342070 q = 1) (hb : d343678 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342071 q = 1) (hb : d343679 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342071, d343679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342071, d343679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342072 q = 1) (hb : d343680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342072, d343680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342072, d343680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93312 (p : Pattern) (ha : d342078 p = 1) (hb : d343686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342073 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
    | true =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
  have h2 (q : Pattern) (ha : d342074 q = 1) (hb : d343682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342074, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342074, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342075 q = 1) (hb : d343683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342075, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342075, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342076 q = 1) (hb : d343684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342076, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342076, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342077 q = 1) (hb : d343685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342077, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342077, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342078 q = 1) (hb : d343686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342078, d343686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342078, d343686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93313 (p : Pattern) (ha : d342081 p = 1) (hb : d343689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342065 q = 1) (hb : d343673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342066 q = 1) (hb : d343674 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342067 q = 1) (hb : d343675 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342067, d343675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342067, d343675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342081 q = 1) (hb : d343689 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342081, d343689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342081, d343689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93314 (p : Pattern) (ha : d342082 p = 1) (hb : d343690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342069 q = 1) (hb : d343677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342070 q = 1) (hb : d343678 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342071 q = 1) (hb : d343679 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342071, d343679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342071, d343679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342082 q = 1) (hb : d343690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342082, d343690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342082, d343690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93315 (p : Pattern) (ha : d342088 p = 1) (hb : d343696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342073 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
    | true =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
  have h2 (q : Pattern) (ha : d342074 q = 1) (hb : d343682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342074, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342074, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342075 q = 1) (hb : d343683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342075, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342075, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342076 q = 1) (hb : d343684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342076, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342076, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342077 q = 1) (hb : d343685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342077, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342077, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342083 q = 1) (hb : d343691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342083, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93313 q ha hb
    | true =>
      simp only [d342083, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93314 q ha hb
  have h7 (q : Pattern) (ha : d342084 q = 1) (hb : d343692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342084, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342084, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342085 q = 1) (hb : d343693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342085, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342085, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342086 q = 1) (hb : d343694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342086, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342086, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342087 q = 1) (hb : d343695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342087, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342087, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342088 q = 1) (hb : d343696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342088, d343696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342088, d343696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93316 (p : Pattern) (ha : d342093 p = 1) (hb : d343701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342065 q = 1) (hb : d343673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342066 q = 1) (hb : d343674 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342092 q = 1) (hb : d343700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342092, d343700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342092, d343700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342093 q = 1) (hb : d343701 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342093, d343701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342093, d343701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93317 (p : Pattern) (ha : d342095 p = 1) (hb : d343703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342069 q = 1) (hb : d343677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342070 q = 1) (hb : d343678 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342094 q = 1) (hb : d343702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342094, d343702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342094, d343702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342095 q = 1) (hb : d343703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342095, d343703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342095, d343703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93318 (p : Pattern) (ha : d342102 p = 1) (hb : d343710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342065 q = 1) (hb : d343673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342100 q = 1) (hb : d343708 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342100, d343708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342100, d343708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342101 q = 1) (hb : d343709 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342101, d343709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342101, d343709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342102 q = 1) (hb : d343710 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342102, d343710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342102, d343710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93319 (p : Pattern) (ha : d342105 p = 1) (hb : d343713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342069 q = 1) (hb : d343677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342103 q = 1) (hb : d343711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342103, d343711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342103, d343711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342104 q = 1) (hb : d343712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342104, d343712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342104, d343712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342105 q = 1) (hb : d343713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342105, d343713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342105, d343713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93320 (p : Pattern) (ha : d342112 p = 1) (hb : d343720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341791 q = 1) (hb : d343400 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93261 q ha hb
    | true =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341792 q = 1) (hb : d343401 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342109 q = 1) (hb : d343717 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342109, d343717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342109, d343717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342110 q = 1) (hb : d343718 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342110, d343718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342110, d343718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342111 q = 1) (hb : d343719 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342111, d343719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342111, d343719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d341996 q = 1) (hb : d343604 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93298 q ha hb
    | true =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d341997 q = 1) (hb : d343605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d341998 q = 1) (hb : d343606 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341998, d343606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341998, d343606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341999 q = 1) (hb : d343607 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341999, d343607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341999, d343607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d342000 q = 1) (hb : d343608 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342000, d343608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342000, d343608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342112 q = 1) (hb : d343720 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342112, d343720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342112, d343720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93321 (p : Pattern) (ha : d342117 p = 1) (hb : d343725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341791 q = 1) (hb : d343400 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93261 q ha hb
    | true =>
      simp only [d341791, d343400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d341792 q = 1) (hb : d343401 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341792, d343401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341996 q = 1) (hb : d343604 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93298 q ha hb
    | true =>
      simp only [d341996, d343604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341997 q = 1) (hb : d343605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341997, d343605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341998 q = 1) (hb : d343606 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341998, d343606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d341998, d343606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341999 q = 1) (hb : d343607 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d341999, d343607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341999, d343607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342000 q = 1) (hb : d343608 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342000, d343608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342000, d343608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342002 q = 1) (hb : d343610 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93299 q ha hb
    | true =>
      simp only [d342002, d343610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342003 q = 1) (hb : d343611 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342003, d343611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d342004 q = 1) (hb : d343612 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342004, d343612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342023 q = 1) (hb : d343631 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d342023, d343631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342023, d343631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d342024 q = 1) (hb : d343632 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d342024, d343632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342024, d343632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342117 q = 1) (hb : d343725 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d342117, d343725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342117, d343725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro93322 (p : Pattern) (ha : d342124 p = 1) (hb : d343732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342113 q = 1) (hb : d343721 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342113, d343721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93320 q ha hb
    | true =>
      simp only [d342113, d343721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342114 q = 1) (hb : d343722 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342114, d343722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342114, d343722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342115 q = 1) (hb : d343723 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342115, d343723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342115, d343723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342116 q = 1) (hb : d343724 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342116, d343724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342116, d343724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342118 q = 1) (hb : d343726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342118, d343726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93321 q ha hb
    | true =>
      simp only [d342118, d343726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342119 q = 1) (hb : d343727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342119, d343727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342119, d343727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342120 q = 1) (hb : d343728 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342120, d343728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342120, d343728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342121 q = 1) (hb : d343729 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342121, d343729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342121, d343729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342122 q = 1) (hb : d343730 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342122, d343730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342122, d343730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342026 q = 1) (hb : d343634 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
    | true =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342027 q = 1) (hb : d343635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d342028 q = 1) (hb : d343636 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342028, d343636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342028, d343636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d342029 q = 1) (hb : d343637 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342029, d343637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342029, d343637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d342123 q = 1) (hb : d343731 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342123, d343731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342123, d343731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d342124 q = 1) (hb : d343732 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342124, d343732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342124, d343732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93323 (p : Pattern) (ha : d342128 p = 1) (hb : d343736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342026 q = 1) (hb : d343634 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
    | true =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342027 q = 1) (hb : d343635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342028 q = 1) (hb : d343636 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342028, d343636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342028, d343636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342029 q = 1) (hb : d343637 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342029, d343637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342029, d343637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342036 q = 1) (hb : d343644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342036, d343644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342037 q = 1) (hb : d343645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342037, d343645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342038 q = 1) (hb : d343646 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342038, d343646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342038, d343646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342046 q = 1) (hb : d343654 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342046, d343654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342046, d343654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342128 q = 1) (hb : d343736 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342128, d343736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342128, d343736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93324 (p : Pattern) (ha : d342134 p = 1) (hb : d343742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342125 q = 1) (hb : d343733 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342125, d343733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93322 q ha hb
    | true =>
      simp only [d342125, d343733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93304 q ha hb
  have h2 (q : Pattern) (ha : d342126 q = 1) (hb : d343734 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342126, d343734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342126, d343734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342127 q = 1) (hb : d343735 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342127, d343735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342127, d343735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342129 q = 1) (hb : d343737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342129, d343737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93304 q ha hb
    | true =>
      simp only [d342129, d343737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93323 q ha hb
  have h5 (q : Pattern) (ha : d342130 q = 1) (hb : d343738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342130, d343738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342130, d343738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342131 q = 1) (hb : d343739 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342131, d343739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342131, d343739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342132 q = 1) (hb : d343740 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342132, d343740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342132, d343740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342048 q = 1) (hb : d343656 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342048, d343656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93304 q ha hb
    | true =>
      simp only [d342048, d343656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93306 q ha hb
  have h9 (q : Pattern) (ha : d342049 q = 1) (hb : d343657 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342049, d343657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342049, d343657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342050 q = 1) (hb : d343658 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342050, d343658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342050, d343658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342052 q = 1) (hb : d343660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342052, d343660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93306 q ha hb
    | true =>
      simp only [d342052, d343660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93307 q ha hb
  have h12 (q : Pattern) (ha : d342053 q = 1) (hb : d343661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342053, d343661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342053, d343661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d342054 q = 1) (hb : d343662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342054, d343662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342054, d343662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342055 q = 1) (hb : d343663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342055, d343663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342055, d343663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d342133 q = 1) (hb : d343741 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d342133, d343741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342133, d343741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342134 q = 1) (hb : d343742 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d342134, d343742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342134, d343742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro93325 (p : Pattern) (ha : d342140 p = 1) (hb : d343748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342135 q = 1) (hb : d343743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342135, d343743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93324 q ha hb
    | true =>
      simp only [d342135, d343743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342136 q = 1) (hb : d343744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342136, d343744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342136, d343744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342137 q = 1) (hb : d343745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342137, d343745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342137, d343745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342138 q = 1) (hb : d343746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342138, d343746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342138, d343746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342139 q = 1) (hb : d343747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342139, d343747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342139, d343747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342140 q = 1) (hb : d343748 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342140, d343748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342140, d343748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93326 (p : Pattern) (ha : d342146 p = 1) (hb : d343754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342143 q = 1) (hb : d343751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342143, d343751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342143, d343751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342144 q = 1) (hb : d343752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342144, d343752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342144, d343752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342145 q = 1) (hb : d343753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342145, d343753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342145, d343753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342146 q = 1) (hb : d343754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342146, d343754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342146, d343754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93327 (p : Pattern) (ha : d342152 p = 1) (hb : d343760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342096 q = 1) (hb : d343704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342096, d343704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93316 q ha hb
    | true =>
      simp only [d342096, d343704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93317 q ha hb
  have h2 (q : Pattern) (ha : d342097 q = 1) (hb : d343705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342097, d343705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342097, d343705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342098 q = 1) (hb : d343706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342098, d343706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342098, d343706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342099 q = 1) (hb : d343707 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342099, d343707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342099, d343707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342106 q = 1) (hb : d343714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342106, d343714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93318 q ha hb
    | true =>
      simp only [d342106, d343714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93319 q ha hb
  have h6 (q : Pattern) (ha : d342107 q = 1) (hb : d343715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342107, d343715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342107, d343715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342108 q = 1) (hb : d343716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342108, d343716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342108, d343716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342141 q = 1) (hb : d343749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342141, d343749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93325 q ha hb
    | true =>
      simp only [d342141, d343749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d342073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d342142 q = 1) (hb : d343750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342142, d343750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342142, d343750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d342147 q = 1) (hb : d343755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342147, d343755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93326 q ha hb
    | true =>
      simp only [d342147, d343755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d342148 q = 1) (hb : d343756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342148, d343756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342148, d343756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342149 q = 1) (hb : d343757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342149, d343757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342149, d343757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342150 q = 1) (hb : d343758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342150, d343758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342150, d343758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d342151 q = 1) (hb : d343759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342151, d343759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342151, d343759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342152 q = 1) (hb : d343760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342152, d343760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342152, d343760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro93328 (p : Pattern) (ha : d342153 p = 1) (hb : d343761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342065 q = 1) (hb : d343673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342066 q = 1) (hb : d343674 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342066, d343674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342092 q = 1) (hb : d343700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342092, d343700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342092, d343700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342153 q = 1) (hb : d343761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342153, d343761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342153, d343761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93329 (p : Pattern) (ha : d342154 p = 1) (hb : d343762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342069 q = 1) (hb : d343677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342070 q = 1) (hb : d343678 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342070, d343678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342094 q = 1) (hb : d343702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342094, d343702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342094, d343702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342154 q = 1) (hb : d343762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342154, d343762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342154, d343762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93330 (p : Pattern) (ha : d342159 p = 1) (hb : d343767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342065 q = 1) (hb : d343673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342065, d343673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342100 q = 1) (hb : d343708 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342100, d343708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342100, d343708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342101 q = 1) (hb : d343709 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342101, d343709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342101, d343709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342159 q = 1) (hb : d343767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342159, d343767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342159, d343767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93331 (p : Pattern) (ha : d342160 p = 1) (hb : d343768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342063 q = 1) (hb : d343671 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93309 q ha hb
    | true =>
      simp only [d342063, d343671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342064 q = 1) (hb : d343672 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342064, d343672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342069 q = 1) (hb : d343677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342069, d343677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342103 q = 1) (hb : d343711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342103, d343711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342103, d343711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342104 q = 1) (hb : d343712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342104, d343712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342104, d343712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342160 q = 1) (hb : d343768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342160, d343768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342160, d343768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93332 (p : Pattern) (ha : d342164 p = 1) (hb : d343772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342135 q = 1) (hb : d343743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342135, d343743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93324 q ha hb
    | true =>
      simp only [d342135, d343743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342136 q = 1) (hb : d343744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342136, d343744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342136, d343744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342137 q = 1) (hb : d343745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342137, d343745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342137, d343745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342138 q = 1) (hb : d343746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342138, d343746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342138, d343746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342139 q = 1) (hb : d343747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342139, d343747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342139, d343747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342164 q = 1) (hb : d343772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342164, d343772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342164, d343772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93333 (p : Pattern) (ha : d342167 p = 1) (hb : d343775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342059 q = 1) (hb : d343667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93308 q ha hb
    | true =>
      simp only [d342059, d343667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342060 q = 1) (hb : d343668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342060, d343668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342143 q = 1) (hb : d343751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342143, d343751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342143, d343751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342144 q = 1) (hb : d343752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342144, d343752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342144, d343752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342145 q = 1) (hb : d343753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342145, d343753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342145, d343753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342167 q = 1) (hb : d343775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342167, d343775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342167, d343775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93334 (p : Pattern) (ha : d342173 p = 1) (hb : d343781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342096 q = 1) (hb : d343704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342096, d343704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93316 q ha hb
    | true =>
      simp only [d342096, d343704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93317 q ha hb
  have h2 (q : Pattern) (ha : d342097 q = 1) (hb : d343705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342097, d343705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342097, d343705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342098 q = 1) (hb : d343706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342098, d343706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342098, d343706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342099 q = 1) (hb : d343707 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342099, d343707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342099, d343707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342106 q = 1) (hb : d343714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342106, d343714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93318 q ha hb
    | true =>
      simp only [d342106, d343714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93319 q ha hb
  have h6 (q : Pattern) (ha : d342107 q = 1) (hb : d343715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342107, d343715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342107, d343715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342108 q = 1) (hb : d343716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342108, d343716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342108, d343716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342141 q = 1) (hb : d343749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342141, d343749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93325 q ha hb
    | true =>
      simp only [d342141, d343749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d342073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d342142 q = 1) (hb : d343750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342142, d343750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342142, d343750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d342147 q = 1) (hb : d343755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342147, d343755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93326 q ha hb
    | true =>
      simp only [d342147, d343755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d342148 q = 1) (hb : d343756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342148, d343756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342148, d343756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342149 q = 1) (hb : d343757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342149, d343757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342149, d343757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342150 q = 1) (hb : d343758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342150, d343758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342150, d343758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d342151 q = 1) (hb : d343759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342151, d343759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342151, d343759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342155 q = 1) (hb : d343763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342155, d343763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93328 q ha hb
    | true =>
      simp only [d342155, d343763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93329 q ha hb
  have h17 (q : Pattern) (ha : d342156 q = 1) (hb : d343764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342156, d343764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342156, d343764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d342157 q = 1) (hb : d343765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342157, d343765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d342157, d343765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d342158 q = 1) (hb : d343766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342158, d343766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342158, d343766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d342161 q = 1) (hb : d343769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342161, d343769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93330 q ha hb
    | true =>
      simp only [d342161, d343769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93331 q ha hb
  have h21 (q : Pattern) (ha : d342162 q = 1) (hb : d343770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342162, d343770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342162, d343770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d342163 q = 1) (hb : d343771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342163, d343771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d342163, d343771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d342165 q = 1) (hb : d343773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342165, d343773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93332 q ha hb
    | true =>
      simp only [d342165, d343773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93313 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d342083 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d342166 q = 1) (hb : d343774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342166, d343774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d342166, d343774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d342168 q = 1) (hb : d343776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342168, d343776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93333 q ha hb
    | true =>
      simp only [d342168, d343776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d342169 q = 1) (hb : d343777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342169, d343777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d342169, d343777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d342170 q = 1) (hb : d343778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342170, d343778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d342170, d343778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d342171 q = 1) (hb : d343779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342171, d343779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d342171, d343779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d342172 q = 1) (hb : d343780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342172, d343780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d342172, d343780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d342173 q = 1) (hb : d343781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342173, d343781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342173, d343781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro93335 (p : Pattern) (ha : d342180 p = 1) (hb : d343788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342073 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
    | true =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
  have h2 (q : Pattern) (ha : d342074 q = 1) (hb : d343682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342074, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342074, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342075 q = 1) (hb : d343683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342075, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342075, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342076 q = 1) (hb : d343684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342076, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342076, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342077 q = 1) (hb : d343685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342077, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342077, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342175 q = 1) (hb : d343783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342175, d343783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
    | true =>
      simp only [d342175, d343783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342176 q = 1) (hb : d343784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342176, d343784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342176, d343784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342177 q = 1) (hb : d343785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342177, d343785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342177, d343785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342178 q = 1) (hb : d343786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342178, d343786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342178, d343786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342179 q = 1) (hb : d343787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342179, d343787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342179, d343787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342180 q = 1) (hb : d343788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342180, d343788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342180, d343788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93336 (p : Pattern) (ha : d342186 p = 1) (hb : d343794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342175 q = 1) (hb : d343783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342175, d343783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
    | true =>
      simp only [d342175, d343783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342176 q = 1) (hb : d343784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342176, d343784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342176, d343784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342177 q = 1) (hb : d343785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342177, d343785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342177, d343785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342178 q = 1) (hb : d343786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342178, d343786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342178, d343786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342179 q = 1) (hb : d343787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342179, d343787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342179, d343787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342181 q = 1) (hb : d343789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342181, d343789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93314 q ha hb
    | true =>
      simp only [d342181, d343789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342182 q = 1) (hb : d343790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342182, d343790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342182, d343790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342183 q = 1) (hb : d343791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342183, d343791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342183, d343791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342184 q = 1) (hb : d343792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342184, d343792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342184, d343792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342185 q = 1) (hb : d343793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342185, d343793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342185, d343793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342186 q = 1) (hb : d343794 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342186, d343794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342186, d343794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93337 (p : Pattern) (ha : d342193 p = 1) (hb : d343801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342165 q = 1) (hb : d343773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342165, d343773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93332 q ha hb
    | true =>
      simp only [d342165, d343773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93313 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342083 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342166 q = 1) (hb : d343774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342166, d343774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342166, d343774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d342168 q = 1) (hb : d343776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342168, d343776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93333 q ha hb
    | true =>
      simp only [d342168, d343776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342169 q = 1) (hb : d343777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342169, d343777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342169, d343777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342170 q = 1) (hb : d343778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342170, d343778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342170, d343778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342191 q = 1) (hb : d343799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342191, d343799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342191, d343799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342192 q = 1) (hb : d343800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342192, d343800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342192, d343800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342193 q = 1) (hb : d343801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342193, d343801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342193, d343801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro93338 (p : Pattern) (ha : d342195 p = 1) (hb : d343803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342181 q = 1) (hb : d343789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342181, d343789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93314 q ha hb
    | true =>
      simp only [d342181, d343789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342182 q = 1) (hb : d343790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342182, d343790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342182, d343790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342183 q = 1) (hb : d343791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342183, d343791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342183, d343791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342184 q = 1) (hb : d343792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342184, d343792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342184, d343792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342185 q = 1) (hb : d343793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342185, d343793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342185, d343793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342195 q = 1) (hb : d343803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342195, d343803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342195, d343803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93339 (p : Pattern) (ha : d342215 p = 1) (hb : d343823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342201 q = 1) (hb : d343809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342201, d343809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342201, d343809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93320 q ha hb
  have h2 (q : Pattern) (ha : d342113 q = 1) (hb : d343721 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342113, d343721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93320 q ha hb
    | true =>
      simp only [d342113, d343721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342202 q = 1) (hb : d343810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342202, d343810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342202, d343810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342114 q = 1) (hb : d343722 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342114, d343722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342114, d343722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342203 q = 1) (hb : d343811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342203, d343811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342203, d343811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342204 q = 1) (hb : d343812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342204, d343812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342204, d343812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342205 q = 1) (hb : d343813 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342205, d343813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342205, d343813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93321 q ha hb
  have h8 (q : Pattern) (ha : d342118 q = 1) (hb : d343726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342118, d343726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93321 q ha hb
    | true =>
      simp only [d342118, d343726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342206 q = 1) (hb : d343814 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342206, d343814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342206, d343814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342119 q = 1) (hb : d343727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342119, d343727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342119, d343727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342207 q = 1) (hb : d343815 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342207, d343815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342207, d343815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d342208 q = 1) (hb : d343816 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342208, d343816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342208, d343816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342209 q = 1) (hb : d343817 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342209, d343817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342209, d343817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342210 q = 1) (hb : d343818 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342210, d343818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342210, d343818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
  have h15 (q : Pattern) (ha : d342026 q = 1) (hb : d343634 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
    | true =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d342211 q = 1) (hb : d343819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342211, d343819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d342211, d343819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342027 q = 1) (hb : d343635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d342212 q = 1) (hb : d343820 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342212, d343820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d342212, d343820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d342213 q = 1) (hb : d343821 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342213, d343821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d342213, d343821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d342214 q = 1) (hb : d343822 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342214, d343822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342214, d343822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d342215 q = 1) (hb : d343823 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342215, d343823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342215, d343823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro93340 (p : Pattern) (ha : d342230 p = 1) (hb : d343838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342216 q = 1) (hb : d343824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342216, d343824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342216, d343824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93300 q ha hb
  have h2 (q : Pattern) (ha : d342008 q = 1) (hb : d343616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342008, d343616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93300 q ha hb
    | true =>
      simp only [d342008, d343616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342217 q = 1) (hb : d343825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342217, d343825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342217, d343825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342009 q = 1) (hb : d343617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342009, d343617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342009, d343617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342218 q = 1) (hb : d343826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342218, d343826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342218, d343826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342219 q = 1) (hb : d343827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342219, d343827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342219, d343827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342220 q = 1) (hb : d343828 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342220, d343828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342220, d343828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93301 q ha hb
  have h8 (q : Pattern) (ha : d342018 q = 1) (hb : d343626 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342018, d343626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93301 q ha hb
    | true =>
      simp only [d342018, d343626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342221 q = 1) (hb : d343829 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342221, d343829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342221, d343829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342019 q = 1) (hb : d343627 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342019, d343627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342019, d343627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342222 q = 1) (hb : d343830 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342222, d343830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342222, d343830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d342223 q = 1) (hb : d343831 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342223, d343831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342223, d343831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342224 q = 1) (hb : d343832 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342224, d343832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342224, d343832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342210 q = 1) (hb : d343818 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342210, d343818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342210, d343818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
  have h15 (q : Pattern) (ha : d342026 q = 1) (hb : d343634 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
    | true =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d342211 q = 1) (hb : d343819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342211, d343819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d342211, d343819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342027 q = 1) (hb : d343635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d342212 q = 1) (hb : d343820 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342212, d343820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d342212, d343820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d342213 q = 1) (hb : d343821 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342213, d343821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d342213, d343821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d342225 q = 1) (hb : d343833 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
  have h21 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d342226 q = 1) (hb : d343834 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d342227 q = 1) (hb : d343835 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d342228 q = 1) (hb : d343836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d342229 q = 1) (hb : d343837 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342229, d343837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d342229, d343837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d342230 q = 1) (hb : d343838 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342230, d343838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342230, d343838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro93341 (p : Pattern) (ha : d342235 p = 1) (hb : d343843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342210 q = 1) (hb : d343818 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342210, d343818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342210, d343818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
  have h2 (q : Pattern) (ha : d342026 q = 1) (hb : d343634 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93302 q ha hb
    | true =>
      simp only [d342026, d343634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342211 q = 1) (hb : d343819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342211, d343819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342211, d343819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342027 q = 1) (hb : d343635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342027, d343635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342212 q = 1) (hb : d343820 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342212, d343820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342212, d343820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342213 q = 1) (hb : d343821 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342213, d343821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342213, d343821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342225 q = 1) (hb : d343833 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
  have h8 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342226 q = 1) (hb : d343834 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342227 q = 1) (hb : d343835 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d342228 q = 1) (hb : d343836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342229 q = 1) (hb : d343837 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342229, d343837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342229, d343837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342234 q = 1) (hb : d343842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342234, d343842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342234, d343842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d342235 q = 1) (hb : d343843 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342235, d343843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342235, d343843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93342 (p : Pattern) (ha : d342245 p = 1) (hb : d343853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342240 q = 1) (hb : d343848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342240, d343848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342240, d343848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93305 q ha hb
  have h2 (q : Pattern) (ha : d342041 q = 1) (hb : d343649 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342041, d343649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93305 q ha hb
    | true =>
      simp only [d342041, d343649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342241 q = 1) (hb : d343849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342241, d343849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342241, d343849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342042 q = 1) (hb : d343650 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342042, d343650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342042, d343650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342242 q = 1) (hb : d343850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342242, d343850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342242, d343850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342243 q = 1) (hb : d343851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342243, d343851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342243, d343851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342225 q = 1) (hb : d343833 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
  have h8 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342226 q = 1) (hb : d343834 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d342227 q = 1) (hb : d343835 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d342228 q = 1) (hb : d343836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d342244 q = 1) (hb : d343852 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342244, d343852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342244, d343852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342234 q = 1) (hb : d343842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342234, d343842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342234, d343842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d342245 q = 1) (hb : d343853 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342245, d343853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342245, d343853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93343 (p : Pattern) (ha : d342249 p = 1) (hb : d343857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342225 q = 1) (hb : d343833 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342225, d343833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
  have h2 (q : Pattern) (ha : d342034 q = 1) (hb : d343642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93303 q ha hb
    | true =>
      simp only [d342034, d343642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342226 q = 1) (hb : d343834 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342226, d343834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342035 q = 1) (hb : d343643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342035, d343643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342227 q = 1) (hb : d343835 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342227, d343835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342228 q = 1) (hb : d343836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342228, d343836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342234 q = 1) (hb : d343842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d342234, d343842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342234, d343842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342249 q = 1) (hb : d343857 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d342249, d343857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342249, d343857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93344 (p : Pattern) (ha : d342255 p = 1) (hb : d343863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342231 q = 1) (hb : d343839 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342231, d343839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93339 q ha hb
    | true =>
      simp only [d342231, d343839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93340 q ha hb
  have h2 (q : Pattern) (ha : d342232 q = 1) (hb : d343840 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342232, d343840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342232, d343840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342233 q = 1) (hb : d343841 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342233, d343841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342233, d343841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342236 q = 1) (hb : d343844 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342236, d343844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93340 q ha hb
    | true =>
      simp only [d342236, d343844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93341 q ha hb
  have h5 (q : Pattern) (ha : d342237 q = 1) (hb : d343845 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342237, d343845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342237, d343845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342238 q = 1) (hb : d343846 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342238, d343846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342238, d343846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342239 q = 1) (hb : d343847 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342239, d343847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342239, d343847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342246 q = 1) (hb : d343854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342246, d343854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93340 q ha hb
    | true =>
      simp only [d342246, d343854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93342 q ha hb
  have h9 (q : Pattern) (ha : d342247 q = 1) (hb : d343855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342247, d343855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342247, d343855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342248 q = 1) (hb : d343856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342248, d343856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342248, d343856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342250 q = 1) (hb : d343858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342250, d343858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93342 q ha hb
    | true =>
      simp only [d342250, d343858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93343 q ha hb
  have h12 (q : Pattern) (ha : d342251 q = 1) (hb : d343859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342251, d343859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342251, d343859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d342252 q = 1) (hb : d343860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342252, d343860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342252, d343860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342253 q = 1) (hb : d343861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342253, d343861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342253, d343861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d342254 q = 1) (hb : d343862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d342254, d343862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342254, d343862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342255 q = 1) (hb : d343863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d342255, d343863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342255, d343863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro93345 (p : Pattern) (ha : d342260 p = 1) (hb : d343868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342246 q = 1) (hb : d343854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342246, d343854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93340 q ha hb
    | true =>
      simp only [d342246, d343854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93342 q ha hb
  have h2 (q : Pattern) (ha : d342247 q = 1) (hb : d343855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342247, d343855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342247, d343855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342248 q = 1) (hb : d343856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342248, d343856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342248, d343856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342250 q = 1) (hb : d343858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342250, d343858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93342 q ha hb
    | true =>
      simp only [d342250, d343858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93343 q ha hb
  have h5 (q : Pattern) (ha : d342251 q = 1) (hb : d343859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342251, d343859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342251, d343859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342252 q = 1) (hb : d343860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342252, d343860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342252, d343860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342253 q = 1) (hb : d343861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342253, d343861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342253, d343861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342258 q = 1) (hb : d343866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342258, d343866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342258, d343866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d342259 q = 1) (hb : d343867 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d342259, d343867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342259, d343867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342260 q = 1) (hb : d343868 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d342260, d343868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342260, d343868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro93346 (p : Pattern) (ha : d342266 p = 1) (hb : d343874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342256 q = 1) (hb : d343864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342256, d343864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93344 q ha hb
    | true =>
      simp only [d342256, d343864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342257 q = 1) (hb : d343865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342257, d343865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342257, d343865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342261 q = 1) (hb : d343869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342261, d343869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93345 q ha hb
    | true =>
      simp only [d342261, d343869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342262 q = 1) (hb : d343870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342262, d343870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342262, d343870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342263 q = 1) (hb : d343871 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342263, d343871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342263, d343871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342264 q = 1) (hb : d343872 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342264, d343872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342264, d343872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342265 q = 1) (hb : d343873 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342265, d343873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342265, d343873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342266 q = 1) (hb : d343874 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342266, d343874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342266, d343874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93347 (p : Pattern) (ha : d342268 p = 1) (hb : d343876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342250 q = 1) (hb : d343858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d342250, d343858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93342 q ha hb
    | true =>
      simp only [d342250, d343858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93343 q ha hb
  have h2 (q : Pattern) (ha : d342251 q = 1) (hb : d343859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d342251, d343859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342251, d343859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342252 q = 1) (hb : d343860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d342252, d343860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342252, d343860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342258 q = 1) (hb : d343866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d342258, d343866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342258, d343866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342267 q = 1) (hb : d343875 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d342267, d343875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342267, d343875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342268 q = 1) (hb : d343876 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d342268, d343876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342268, d343876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93348 (p : Pattern) (ha : d342274 p = 1) (hb : d343882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342261 q = 1) (hb : d343869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342261, d343869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93345 q ha hb
    | true =>
      simp only [d342261, d343869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342262 q = 1) (hb : d343870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342262, d343870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342262, d343870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342269 q = 1) (hb : d343877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342269, d343877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93347 q ha hb
    | true =>
      simp only [d342269, d343877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342270 q = 1) (hb : d343878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342270, d343878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342270, d343878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342271 q = 1) (hb : d343879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342271, d343879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342271, d343879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342272 q = 1) (hb : d343880 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342272, d343880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342272, d343880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d342273 q = 1) (hb : d343881 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342273, d343881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342273, d343881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d342274 q = 1) (hb : d343882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342274, d343882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342274, d343882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro93349 (p : Pattern) (ha : d342285 p = 1) (hb : d343888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342261 q = 1) (hb : d343869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342261, d343869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93345 q ha hb
    | true =>
      simp only [d342261, d343869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342262 q = 1) (hb : d343870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342262, d343870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342262, d343870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342282 q = 1) (hb : d343885 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342282, d343885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342282, d343885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342283 q = 1) (hb : d343886 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342283, d343886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342283, d343886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342284 q = 1) (hb : d343887 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342284, d343887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342284, d343887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342285 q = 1) (hb : d343888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342285, d343888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342285, d343888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93350 (p : Pattern) (ha : d342291 p = 1) (hb : d343894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342275 q = 1) (hb : d343883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342275, d343883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93346 q ha hb
    | true =>
      simp only [d342275, d343883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93348 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342280 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342281 q = 1) (hb : d343884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342281, d343884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342281, d343884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d342286 q = 1) (hb : d343889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342286, d343889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93349 q ha hb
    | true =>
      simp only [d342286, d343889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342287 q = 1) (hb : d343890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342287, d343890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342287, d343890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342288 q = 1) (hb : d343891 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342288, d343891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342288, d343891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342289 q = 1) (hb : d343892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342289, d343892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342289, d343892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342290 q = 1) (hb : d343893 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342290, d343893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342290, d343893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342291 q = 1) (hb : d343894 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342291, d343894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342291, d343894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro93351 (p : Pattern) (ha : d342279 p = 1) (hb : d343899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342269 q = 1) (hb : d343877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d342269, d343877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93347 q ha hb
    | true =>
      simp only [d342269, d343877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342270 q = 1) (hb : d343878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d342270, d343878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342270, d343878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342276 q = 1) (hb : d343896 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d342276, d343896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342276, d343896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342277 q = 1) (hb : d343897 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d342277, d343897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342277, d343897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342278 q = 1) (hb : d343898 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d342278, d343898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342278, d343898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342279 q = 1) (hb : d343899 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d342279, d343899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342279, d343899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93352 (p : Pattern) (ha : d342298 p = 1) (hb : d343905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342293 q = 1) (hb : d343900 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342293, d343900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93351 q ha hb
    | true =>
      simp only [d342293, d343900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342294 q = 1) (hb : d343901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342294, d343901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342294, d343901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342295 q = 1) (hb : d343902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342295, d343902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342295, d343902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342296 q = 1) (hb : d343903 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342296, d343903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342296, d343903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342297 q = 1) (hb : d343904 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342297, d343904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342297, d343904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342298 q = 1) (hb : d343905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342298, d343905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342298, d343905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93353 (p : Pattern) (ha : d342304 p = 1) (hb : d343911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342079 q = 1) (hb : d343687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342079, d343687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342079, d343687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93312 q ha hb
  have h2 (q : Pattern) (ha : d342080 q = 1) (hb : d343688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342080, d343688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342080, d343688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342089 q = 1) (hb : d343697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342089, d343697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93312 q ha hb
    | true =>
      simp only [d342089, d343697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93315 q ha hb
  have h4 (q : Pattern) (ha : d342090 q = 1) (hb : d343698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342090, d343698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342090, d343698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342091 q = 1) (hb : d343699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342091, d343699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342091, d343699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342174 q = 1) (hb : d343782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342174, d343782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93327 q ha hb
    | true =>
      simp only [d342174, d343782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93334 q ha hb
  have h7 (q : Pattern) (ha : d342187 q = 1) (hb : d343795 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342187, d343795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93335 q ha hb
    | true =>
      simp only [d342187, d343795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93336 q ha hb
  have h8 (q : Pattern) (ha : d342188 q = 1) (hb : d343796 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342188, d343796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342188, d343796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342189 q = 1) (hb : d343797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342189, d343797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342189, d343797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d342190 q = 1) (hb : d343798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d342190, d343798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342190, d343798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d342194 q = 1) (hb : d343802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342194, d343802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342194, d343802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93337 q ha hb
  have h12 (q : Pattern) (ha : d342196 q = 1) (hb : d343804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342196, d343804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342196, d343804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93338 q ha hb
  have h13 (q : Pattern) (ha : d342197 q = 1) (hb : d343805 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342197, d343805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342197, d343805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d342198 q = 1) (hb : d343806 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342198, d343806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342198, d343806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d342199 q = 1) (hb : d343807 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d342199, d343807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d342199, d343807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d342200 q = 1) (hb : d343808 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d342200, d343808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342200, d343808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342292 q = 1) (hb : d343895 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342292, d343895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342292, d343895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93350 q ha hb
  have h18 (q : Pattern) (ha : d342299 q = 1) (hb : d343906 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342299, d343906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342299, d343906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93352 q ha hb
  have h19 (q : Pattern) (ha : d342300 q = 1) (hb : d343907 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342300, d343907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d342300, d343907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d342301 q = 1) (hb : d343908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342301, d343908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d342301, d343908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d342302 q = 1) (hb : d343909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d342302, d343909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d342302, d343909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d342303 q = 1) (hb : d343910 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d342303, d343910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d342303, d343910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d342304 q = 1) (hb : d343911 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d342304, d343911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d342304, d343911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro93354 (p : Pattern) (ha : d342310 p = 1) (hb : d343917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342305 q = 1) (hb : d343912 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d342305, d343912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342305, d343912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93353 q ha hb
  have h2 (q : Pattern) (ha : d342306 q = 1) (hb : d343913 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d342306, d343913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342306, d343913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342307 q = 1) (hb : d343914 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d342307, d343914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342307, d343914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342308 q = 1) (hb : d343915 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d342308, d343915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342308, d343915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342309 q = 1) (hb : d343916 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d342309, d343916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342309, d343916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342310 q = 1) (hb : d343917 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d342310, d343917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342310, d343917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93355 (p : Pattern) (ha : d342665 p = 1) (hb : d343923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d341467 q = 1) (hb : d343080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d341467, d343080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93167 q ha hb
    | true =>
      simp only [d341467, d343080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93196 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341717 q = 1) (hb : d343326 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d341717, d343326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341717, d343326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93244 q ha hb
  have h3 (q : Pattern) (ha : d341718 q = 1) (hb : d343327 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d341718, d343327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d341718, d343327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341992 q = 1) (hb : d343600 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d341992, d343600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341992, d343600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93297 q ha hb
  have h5 (q : Pattern) (ha : d341993 q = 1) (hb : d343601 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d341993, d343601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341993, d343601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341994 q = 1) (hb : d343602 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d341994, d343602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341994, d343602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342311 q = 1) (hb : d343918 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d342311, d343918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342311, d343918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93354 q ha hb
  have h8 (q : Pattern) (ha : d342312 q = 1) (hb : d343919 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d342312, d343919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342312, d343919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342313 q = 1) (hb : d343920 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d342313, d343920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342313, d343920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342314 q = 1) (hb : d343921 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d342314, d343921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342314, d343921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d342663 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d342664 q = 1) (hb : d343922 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d342664, d343922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342664, d343922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d342665 q = 1) (hb : d343923 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d342665, d343923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342665, d343923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro93356 (p : Pattern) (ha : d342671 p = 1) (hb : d343929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342666 q = 1) (hb : d343924 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d342666, d343924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93355 q ha hb
    | true =>
      simp only [d342666, d343924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342667 q = 1) (hb : d343925 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d342667, d343925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342667, d343925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342668 q = 1) (hb : d343926 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d342668, d343926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342668, d343926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342669 q = 1) (hb : d343927 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d342669, d343927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342669, d343927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342670 q = 1) (hb : d343928 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d342670, d343928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342670, d343928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342671 q = 1) (hb : d343929 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d342671, d343929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342671, d343929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93357 (p : Pattern) (ha : d342677 p = 1) (hb : d343935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342672 q = 1) (hb : d343930 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d342672, d343930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93356 q ha hb
    | true =>
      simp only [d342672, d343930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342673 q = 1) (hb : d343931 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d342673, d343931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342673, d343931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342674 q = 1) (hb : d343932 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d342674, d343932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342674, d343932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342675 q = 1) (hb : d343933 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d342675, d343933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342675, d343933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342676 q = 1) (hb : d343934 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d342676, d343934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342676, d343934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342677 q = 1) (hb : d343935 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d342677, d343935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342677, d343935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93358 (p : Pattern) (ha : d342683 p = 1) (hb : d343941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342678 q = 1) (hb : d343936 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d342678, d343936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93357 q ha hb
    | true =>
      simp only [d342678, d343936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342679 q = 1) (hb : d343937 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d342679, d343937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342679, d343937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342680 q = 1) (hb : d343938 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d342680, d343938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342680, d343938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342681 q = 1) (hb : d343939 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d342681, d343939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342681, d343939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342682 q = 1) (hb : d343940 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d342682, d343940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342682, d343940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342683 q = 1) (hb : d343941 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d342683, d343941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342683, d343941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93359 (p : Pattern) (ha : d342689 p = 1) (hb : d343947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342684 q = 1) (hb : d343942 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d342684, d343942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93358 q ha hb
    | true =>
      simp only [d342684, d343942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342685 q = 1) (hb : d343943 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d342685, d343943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342685, d343943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342686 q = 1) (hb : d343944 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d342686, d343944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342686, d343944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342687 q = 1) (hb : d343945 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d342687, d343945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342687, d343945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342688 q = 1) (hb : d343946 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d342688, d343946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342688, d343946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342689 q = 1) (hb : d343947 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d342689, d343947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342689, d343947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93360 (p : Pattern) (ha : d342695 p = 1) (hb : d343953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342690 q = 1) (hb : d343948 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d342690, d343948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93359 q ha hb
    | true =>
      simp only [d342690, d343948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342691 q = 1) (hb : d343949 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d342691, d343949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342691, d343949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342692 q = 1) (hb : d343950 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d342692, d343950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342692, d343950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342693 q = 1) (hb : d343951 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d342693, d343951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342693, d343951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342694 q = 1) (hb : d343952 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d342694, d343952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342694, d343952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342695 q = 1) (hb : d343953 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d342695, d343953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342695, d343953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93361 (p : Pattern) (ha : d342701 p = 1) (hb : d343959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342696 q = 1) (hb : d343954 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d342696, d343954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93360 q ha hb
    | true =>
      simp only [d342696, d343954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342697 q = 1) (hb : d343955 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d342697, d343955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342697, d343955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342698 q = 1) (hb : d343956 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d342698, d343956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342698, d343956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342699 q = 1) (hb : d343957 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d342699, d343957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342699, d343957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342700 q = 1) (hb : d343958 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d342700, d343958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342700, d343958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342701 q = 1) (hb : d343959 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d342701, d343959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342701, d343959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93362 (p : Pattern) (ha : d342707 p = 1) (hb : d343965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342702 q = 1) (hb : d343960 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d342702, d343960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93361 q ha hb
    | true =>
      simp only [d342702, d343960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342703 q = 1) (hb : d343961 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d342703, d343961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342703, d343961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342704 q = 1) (hb : d343962 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d342704, d343962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342704, d343962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342705 q = 1) (hb : d343963 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d342705, d343963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342705, d343963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342706 q = 1) (hb : d343964 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d342706, d343964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342706, d343964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342707 q = 1) (hb : d343965 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d342707, d343965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342707, d343965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93363 (p : Pattern) (ha : d53647 p = 1) (hb : d272403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92770 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92771 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92794 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92795 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
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
theorem andIntro93364 (p : Pattern) (ha : d53655 p = 1) (hb : d272403 p = 1) : d343021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d272403 q = 1) : d342739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d342739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92777 q ha hb
    | true =>
      simp only [d204, d342739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92762 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d272403 q = 1) : d342797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d342797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d342797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d272403 q = 1) : d342798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d342798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, d342798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d272403 q = 1) : d342799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d342799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d342799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d272403 q = 1) : d342800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d342800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d342800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d272403 q = 1) : d343021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d343021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d343021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93365 (p : Pattern) (ha : d53665 p = 1) (hb : d272403 p = 1) : d343067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d272403 q = 1) : d342773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d342773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92781 q ha hb
    | true =>
      simp only [d244, d342773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92767 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d272403 q = 1) : d343063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d343063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d343063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d272403 q = 1) : d343064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d343064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d343064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d272403 q = 1) : d343065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d343065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d343065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d272403 q = 1) : d343066 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d343066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d343066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d272403 q = 1) : d343067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d343067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d343067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93366 (p : Pattern) (ha : d53671 p = 1) (hb : d272403 p = 1) : d343976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d272403 q = 1) : d342802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d342802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92791 q ha hb
    | true =>
      simp only [d292, d342802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92792 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d272403 q = 1) : d342803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d342803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d342803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d272403 q = 1) : d343966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d343966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d343966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d272403 q = 1) : d343967 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d343967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d343967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d272403 q = 1) : d343022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d343022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d343022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93364 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d272403 q = 1) : d343968 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d343968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d343968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d272403 q = 1) : d343969 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d343969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d343969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d272403 q = 1) : d343970 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d343970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d343970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d272403 q = 1) : d343971 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d343971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d343971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d272403 q = 1) : d343068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d343068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d343068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93365 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d272403 q = 1) : d343972 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d343972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d343972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d272403 q = 1) : d343973 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d343973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d343973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d272403 q = 1) : d343974 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d343974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d343974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d272403 q = 1) : d343975 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d343975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d343975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d272403 q = 1) : d343976 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d343976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d343976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93367 (p : Pattern) (ha : d53677 p = 1) (hb : d272403 p = 1) : d343982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93363 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d272403 q = 1) : d343977 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d343977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d343977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93366 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d272403 q = 1) : d343978 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d343978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d343978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d272403 q = 1) : d343979 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d343979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d343979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d272403 q = 1) : d343980 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d343980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d343980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d272403 q = 1) : d343981 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d343981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d343981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d272403 q = 1) : d343982 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d343982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d343982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro93368 (p : Pattern) (ha : d171078 p = 1) (hb : d272403 p = 1) : d343985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d272403 q = 1) : d342859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d342859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92830 q ha hb
    | true =>
      simp only [d16052, d342859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92821 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d272403 q = 1) : d342922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d342922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d342922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d272403 q = 1) : d342923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d342923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d342923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d272403 q = 1) : d342924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d342924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d342924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d272403 q = 1) : d342925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d342925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d342925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171078 q = 1) (hb : d272403 q = 1) : d343985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d343985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d343985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93369 (p : Pattern) (ha : d171089 p = 1) (hb : d272403 p = 1) : d343995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d272403 q = 1) : d342897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d342897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92857 q ha hb
    | true =>
      simp only [d171084, d342897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92825 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d272403 q = 1) : d343991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d343991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, d343991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d272403 q = 1) : d343992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d343992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d343992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d272403 q = 1) : d343993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d343993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, d343993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d272403 q = 1) : d343994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d343994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, d343994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d272403 q = 1) : d343995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d343995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, d343995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93370 (p : Pattern) (ha : d171095 p = 1) (hb : d272403 p = 1) : d344001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d272403 q = 1) : d342927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d342927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92829 q ha hb
    | true =>
      simp only [d16058, d342927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92831 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d272403 q = 1) : d342928 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d342928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d342928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171076 q = 1) (hb : d272403 q = 1) : d343983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d343983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171076, d343983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171077 q = 1) (hb : d272403 q = 1) : d343984 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d343984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171077, d343984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171079 q = 1) (hb : d272403 q = 1) : d343986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d343986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171079, d343986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93368 q ha hb
  have h6 (q : Pattern) (ha : d171080 q = 1) (hb : d272403 q = 1) : d343987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d343987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d343987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171081 q = 1) (hb : d272403 q = 1) : d343988 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d343988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d343988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171082 q = 1) (hb : d272403 q = 1) : d343989 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d343989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d343989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171083 q = 1) (hb : d272403 q = 1) : d343990 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d343990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d343990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171090 q = 1) (hb : d272403 q = 1) : d343996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d343996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171090, d343996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93369 q ha hb
  have h11 (q : Pattern) (ha : d171091 q = 1) (hb : d272403 q = 1) : d343997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d343997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d343997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171092 q = 1) (hb : d272403 q = 1) : d343998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d343998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d343998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171093 q = 1) (hb : d272403 q = 1) : d343999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d343999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d343999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171094 q = 1) (hb : d272403 q = 1) : d344000 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d344000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d344000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171095 q = 1) (hb : d272403 q = 1) : d344001 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d344001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d344001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93371 (p : Pattern) (ha : d171101 p = 1) (hb : d272403 p = 1) : d344007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d272403 q = 1) : d344002 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d344002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, d344002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93370 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d272403 q = 1) : d344003 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d344003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, d344003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d272403 q = 1) : d344004 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d344004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, d344004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d272403 q = 1) : d344005 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d344005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, d344005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d272403 q = 1) : d344006 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d344006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, d344006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d272403 q = 1) : d344007 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d344007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, d344007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93372 (p : Pattern) (ha : d272403 p = 1) (hb : d279792 p = 1) : d344011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28858 q = 1) (hb : d272403 q = 1) : d343108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, d343108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92883 q ha hb
    | true =>
      simp only [d28858, d343108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92871 q ha hb
  have h2 (q : Pattern) (ha : d28859 q = 1) (hb : d272403 q = 1) : d343109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, d343109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, d343109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28860 q = 1) (hb : d272403 q = 1) : d343110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, d343110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28860, d343110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28861 q = 1) (hb : d272403 q = 1) : d343111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, d343111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, d343111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28862 q = 1) (hb : d272403 q = 1) : d343112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, d343112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, d343112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d279792 q = 1) : d344011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279792, d344011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279792, d344011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro93373 (p : Pattern) (ha : d272403 p = 1) (hb : d279803 p = 1) : d344022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d279798 q = 1) : d344017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d279798, d344017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92916 q hb ha
    | true =>
      simp only [d279798, d344017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92877 q hb ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d279799 q = 1) : d344018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d279799, d344018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279799, d344018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d279800 q = 1) : d344019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d279800, d344019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279800, d344019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d279801 q = 1) : d344020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d279801, d344020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279801, d344020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d279802 q = 1) : d344021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d279802, d344021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279802, d344021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d279803 q = 1) : d344022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279803, d344022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279803, d344022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93374 (p : Pattern) (ha : d272403 p = 1) (hb : d279809 p = 1) : d344028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28864 q = 1) (hb : d272403 q = 1) : d343114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28864, d343114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92882 q ha hb
    | true =>
      simp only [d28864, d343114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92884 q ha hb
  have h2 (q : Pattern) (ha : d28865 q = 1) (hb : d272403 q = 1) : d343115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28865, d343115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28865, d343115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d279790 q = 1) : d344009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279790, d344009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d279790, d344009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d279791 q = 1) : d344010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279791, d344010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279791, d344010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d279793 q = 1) : d344012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279793, d344012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279793, d344012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93372 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d279794 q = 1) : d344013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279794, d344013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279794, d344013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d272403 q = 1) (hb : d279795 q = 1) : d344014 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279795, d344014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279795, d344014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d272403 q = 1) (hb : d279796 q = 1) : d344015 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279796, d344015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d279796, d344015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d272403 q = 1) (hb : d279797 q = 1) : d344016 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279797, d344016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279797, d344016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d272403 q = 1) (hb : d279804 q = 1) : d344023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279804, d344023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279804, d344023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93373 q ha hb
  have h11 (q : Pattern) (ha : d272403 q = 1) (hb : d279805 q = 1) : d344024 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279805, d344024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d279805, d344024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d272403 q = 1) (hb : d279806 q = 1) : d344025 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279806, d344025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d279806, d344025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d272403 q = 1) (hb : d279807 q = 1) : d344026 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279807, d344026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d279807, d344026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d272403 q = 1) (hb : d279808 q = 1) : d344027 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279808, d344027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d279808, d344027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d272403 q = 1) (hb : d279809 q = 1) : d344028 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d279809, d344028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d279809, d344028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93375 (p : Pattern) (ha : d272403 p = 1) (hb : d279815 p = 1) : d344034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d279810 q = 1) : d344029 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d279810, d344029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279810, d344029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93374 q ha hb
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d279811 q = 1) : d344030 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d279811, d344030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279811, d344030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d279812 q = 1) : d344031 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d279812, d344031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279812, d344031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d279813 q = 1) : d344032 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d279813, d344032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279813, d344032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d279814 q = 1) : d344033 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d279814, d344033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279814, d344033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d279815 q = 1) : d344034 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d279815, d344034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279815, d344034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93376 (p : Pattern) (ha : d272403 p = 1) (hb : d333343 p = 1) : d344039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38894 q = 1) (hb : d272403 q = 1) : d343373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38894, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92936 q ha hb
    | true =>
      simp only [d38894, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92937 q ha hb
  have h2 (q : Pattern) (ha : d38895 q = 1) (hb : d272403 q = 1) : d343374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38895, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38895, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38896 q = 1) (hb : d272403 q = 1) : d343375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38896, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38896, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38897 q = 1) (hb : d272403 q = 1) : d343376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38897, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38897, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38898 q = 1) (hb : d272403 q = 1) : d343377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38898, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38898, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333343 q = 1) : d344039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333343, d344039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333343, d344039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro93377 (p : Pattern) (ha : d272403 p = 1) (hb : d333354 p = 1) : d344050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333349 q = 1) : d344045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333349, d344045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92977 q hb ha
    | true =>
      simp only [d333349, d344045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92945 q hb ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333350 q = 1) : d344046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333350, d344046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333350, d344046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333351 q = 1) : d344047 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333351, d344047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333351, d344047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333352 q = 1) : d344048 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333352, d344048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333352, d344048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333353 q = 1) : d344049 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333353, d344049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333353, d344049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333354 q = 1) : d344050 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333354, d344050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333354, d344050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93378 (p : Pattern) (ha : d272403 p = 1) (hb : d333360 p = 1) : d344056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38900 q = 1) (hb : d272403 q = 1) : d343379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d38900, d343379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92935 q ha hb
    | true =>
      simp only [d38900, d343379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92938 q ha hb
  have h2 (q : Pattern) (ha : d38901 q = 1) (hb : d272403 q = 1) : d343380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d38901, d343380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38901, d343380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333341 q = 1) : d344037 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333341, d344037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333341, d344037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333342 q = 1) : d344038 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333342, d344038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333342, d344038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333344 q = 1) : d344040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333344, d344040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333344, d344040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93376 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333345 q = 1) : d344041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333345, d344041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333345, d344041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d272403 q = 1) (hb : d333346 q = 1) : d344042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333346, d344042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333346, d344042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d272403 q = 1) (hb : d333347 q = 1) : d344043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333347, d344043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333347, d344043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d272403 q = 1) (hb : d333348 q = 1) : d344044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333348, d344044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333348, d344044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d272403 q = 1) (hb : d333355 q = 1) : d344051 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333355, d344051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333355, d344051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93377 q ha hb
  have h11 (q : Pattern) (ha : d272403 q = 1) (hb : d333356 q = 1) : d344052 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333356, d344052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333356, d344052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d272403 q = 1) (hb : d333357 q = 1) : d344053 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333357, d344053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333357, d344053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d272403 q = 1) (hb : d333358 q = 1) : d344054 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333358, d344054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333358, d344054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d272403 q = 1) (hb : d333359 q = 1) : d344055 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333359, d344055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333359, d344055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d272403 q = 1) (hb : d333360 q = 1) : d344056 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333360, d344056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333360, d344056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93379 (p : Pattern) (ha : d272403 p = 1) (hb : d333366 p = 1) : d344062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333361 q = 1) : d344057 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333361, d344057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333361, d344057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93378 q ha hb
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333362 q = 1) : d344058 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333362, d344058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333362, d344058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333363 q = 1) : d344059 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333363, d344059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333363, d344059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333364 q = 1) : d344060 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333364, d344060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333364, d344060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333365 q = 1) : d344061 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333365, d344061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333365, d344061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333366 q = 1) : d344062 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333366, d344062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333366, d344062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93380 (p : Pattern) (ha : d272403 p = 1) (hb : d333372 p = 1) : d344068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39327 q = 1) (hb : d272403 q = 1) : d343691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39327, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93005 q ha hb
    | true =>
      simp only [d39327, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93006 q ha hb
  have h2 (q : Pattern) (ha : d39328 q = 1) (hb : d272403 q = 1) : d343692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39328, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39328, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39329 q = 1) (hb : d272403 q = 1) : d343693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39329, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39329, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39330 q = 1) (hb : d272403 q = 1) : d343694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39330, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39330, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39331 q = 1) (hb : d272403 q = 1) : d343695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39331, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39331, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333372 q = 1) : d344068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333372, d344068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333372, d344068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro93381 (p : Pattern) (ha : d272403 p = 1) (hb : d333383 p = 1) : d344079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333378 q = 1) : d344074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333378, d344074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93047 q hb ha
    | true =>
      simp only [d333378, d344074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93014 q hb ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333379 q = 1) : d344075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333379, d344075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333379, d344075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333380 q = 1) : d344076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333380, d344076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333380, d344076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333381 q = 1) : d344077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333381, d344077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333381, d344077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333382 q = 1) : d344078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333382, d344078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333382, d344078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333383 q = 1) : d344079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333383, d344079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333383, d344079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93382 (p : Pattern) (ha : d272403 p = 1) (hb : d333389 p = 1) : d344085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39333 q = 1) (hb : d272403 q = 1) : d343697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39333, d343697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93004 q ha hb
    | true =>
      simp only [d39333, d343697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93007 q ha hb
  have h2 (q : Pattern) (ha : d39334 q = 1) (hb : d272403 q = 1) : d343698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39334, d343698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39334, d343698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333370 q = 1) : d344066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333370, d344066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333370, d344066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333371 q = 1) : d344067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333371, d344067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333371, d344067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333373 q = 1) : d344069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333373, d344069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333373, d344069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93380 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333374 q = 1) : d344070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333374, d344070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333374, d344070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d272403 q = 1) (hb : d333375 q = 1) : d344071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333375, d344071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333375, d344071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d272403 q = 1) (hb : d333376 q = 1) : d344072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333376, d344072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333376, d344072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d272403 q = 1) (hb : d333377 q = 1) : d344073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333377, d344073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333377, d344073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d272403 q = 1) (hb : d333384 q = 1) : d344080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333384, d344080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333384, d344080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93381 q ha hb
  have h11 (q : Pattern) (ha : d272403 q = 1) (hb : d333385 q = 1) : d344081 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333385, d344081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333385, d344081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d272403 q = 1) (hb : d333386 q = 1) : d344082 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333386, d344082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333386, d344082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d272403 q = 1) (hb : d333387 q = 1) : d344083 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333387, d344083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333387, d344083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d272403 q = 1) (hb : d333388 q = 1) : d344084 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333388, d344084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333388, d344084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d272403 q = 1) (hb : d333389 q = 1) : d344085 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333389, d344085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333389, d344085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93383 (p : Pattern) (ha : d272403 p = 1) (hb : d333395 p = 1) : d344091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333390 q = 1) : d344086 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333390, d344086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333390, d344086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93382 q ha hb
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333391 q = 1) : d344087 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333391, d344087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333391, d344087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333392 q = 1) : d344088 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333392, d344088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333392, d344088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333393 q = 1) : d344089 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333393, d344089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333393, d344089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333394 q = 1) : d344090 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333394, d344090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333394, d344090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333395 q = 1) : d344091 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333395, d344091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333395, d344091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93384 (p : Pattern) (ha : d272403 p = 1) (hb : d333402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39765 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93075 q ha hb
    | true =>
      simp only [d39765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93076 q ha hb
  have h2 (q : Pattern) (ha : d39766 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39767 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39768 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39769 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333402 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro93385 (p : Pattern) (ha : d272403 p = 1) (hb : d333413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93116 q hb ha
    | true =>
      simp only [d333408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93084 q hb ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93386 (p : Pattern) (ha : d272403 p = 1) (hb : d333419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39771 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93074 q ha hb
    | true =>
      simp only [d39771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93077 q ha hb
  have h2 (q : Pattern) (ha : d39772 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333400 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333401 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333403 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93384 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333404 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d272403 q = 1) (hb : d333405 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d272403 q = 1) (hb : d333406 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d272403 q = 1) (hb : d333407 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d272403 q = 1) (hb : d333414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93385 q ha hb
  have h11 (q : Pattern) (ha : d272403 q = 1) (hb : d333415 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d272403 q = 1) (hb : d333416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d272403 q = 1) (hb : d333417 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d272403 q = 1) (hb : d333418 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d272403 q = 1) (hb : d333419 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro93387 (p : Pattern) (ha : d272403 p = 1) (hb : d333425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333420 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93386 q ha hb
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333421 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333422 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333423 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333424 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333425 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93388 (p : Pattern) (ha : d272403 p = 1) (hb : d333431 p = 1) : d344097 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d272403 q = 1) : d344008 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d344008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93367 q ha hb
    | true =>
      simp only [d171102, d344008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93371 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d279816 q = 1) : d344035 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279816, d344035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d279816, d344035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93375 q ha hb
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d279817 q = 1) : d344036 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279817, d344036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279817, d344036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333367 q = 1) : d344063 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333367, d344063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333367, d344063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93379 q ha hb
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333368 q = 1) : d344064 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333368, d344064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333368, d344064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333369 q = 1) : d344065 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333369, d344065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333369, d344065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d272403 q = 1) (hb : d333396 q = 1) : d344092 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333396, d344092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333396, d344092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93383 q ha hb
  have h8 (q : Pattern) (ha : d272403 q = 1) (hb : d333397 q = 1) : d344093 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333397, d344093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333397, d344093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d272403 q = 1) (hb : d333398 q = 1) : d344094 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333398, d344094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333398, d344094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d272403 q = 1) (hb : d333399 q = 1) : d344095 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333399, d344095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333399, d344095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d272403 q = 1) (hb : d333426 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93387 q ha hb
  have h12 (q : Pattern) (ha : d272403 q = 1) (hb : d333427 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d272403 q = 1) (hb : d333428 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d272403 q = 1) (hb : d333429 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d272403 q = 1) (hb : d333430 q = 1) : d344096 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d333430, d344096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333430, d344096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d272403 q = 1) (hb : d333431 q = 1) : d344097 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d333431, d344097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d333431, d344097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro93389 (p : Pattern) (ha : d272403 p = 1) (hb : d333437 p = 1) : d344103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333432 q = 1) : d344098 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d333432, d344098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93388 q ha hb
    | true =>
      simp only [d333432, d344098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333433 q = 1) : d344099 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d333433, d344099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333433, d344099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333434 q = 1) : d344100 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d333434, d344100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333434, d344100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333435 q = 1) : d344101 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d333435, d344101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333435, d344101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333436 q = 1) : d344102 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d333436, d344102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333436, d344102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d272403 q = 1) (hb : d333437 q = 1) : d344103 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d333437, d344103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333437, d344103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93390 (p : Pattern) (ha : d333443 p = 1) (hb : d338652 p = 1) : d344109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d272403 q = 1) (hb : d333438 q = 1) : d344104 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d333438, d344104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93389 q ha hb
    | true =>
      simp only [d333438, d344104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d272403 q = 1) (hb : d333439 q = 1) : d344105 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d333439, d344105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333439, d344105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d272403 q = 1) (hb : d333440 q = 1) : d344106 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d333440, d344106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333440, d344106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d272403 q = 1) (hb : d333441 q = 1) : d344107 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d333441, d344107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333441, d344107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d272403 q = 1) (hb : d333442 q = 1) : d344108 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d333442, d344108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333442, d344108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d333443 q = 1) (hb : d338652 q = 1) : d344109 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d333443, d338652, d344109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d333443, d338652, d344109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93391 (p : Pattern) (ha : d333449 p = 1) (hb : d338652 p = 1) : d344115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d333444 q = 1) (hb : d338652 q = 1) : d344110 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d333444, d344110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93390 q ha hb
    | true =>
      simp only [d333444, d344110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d333445 q = 1) (hb : d338652 q = 1) : d344111 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d333445, d344111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333445, d344111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d333446 q = 1) (hb : d338652 q = 1) : d344112 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d333446, d344112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333446, d344112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d333447 q = 1) (hb : d338652 q = 1) : d344113 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d333447, d344113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333447, d344113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d333448 q = 1) (hb : d338652 q = 1) : d344114 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d333448, d344114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333448, d344114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d333449 q = 1) (hb : d338652 q = 1) : d344115 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d333449, d344115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333449, d344115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93392 (p : Pattern) (ha : d333455 p = 1) (hb : d338652 p = 1) : d344121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d333450 q = 1) (hb : d338652 q = 1) : d344116 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d333450, d344116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93391 q ha hb
    | true =>
      simp only [d333450, d344116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d333451 q = 1) (hb : d338652 q = 1) : d344117 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d333451, d344117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333451, d344117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d333452 q = 1) (hb : d338652 q = 1) : d344118 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d333452, d344118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333452, d344118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d333453 q = 1) (hb : d338652 q = 1) : d344119 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d333453, d344119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333453, d344119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d333454 q = 1) (hb : d338652 q = 1) : d344120 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d333454, d344120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333454, d344120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d333455 q = 1) (hb : d338652 q = 1) : d344121 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d333455, d344121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333455, d344121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93393 (p : Pattern) (ha : d333461 p = 1) (hb : d338652 p = 1) : d344127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d333456 q = 1) (hb : d338652 q = 1) : d344122 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d333456, d344122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93392 q ha hb
    | true =>
      simp only [d333456, d344122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d333457 q = 1) (hb : d338652 q = 1) : d344123 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d333457, d344123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333457, d344123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d333458 q = 1) (hb : d338652 q = 1) : d344124 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d333458, d344124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333458, d344124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d333459 q = 1) (hb : d338652 q = 1) : d344125 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d333459, d344125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333459, d344125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d333460 q = 1) (hb : d338652 q = 1) : d344126 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d333460, d344126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333460, d344126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d333461 q = 1) (hb : d338652 q = 1) : d344127 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d333461, d344127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333461, d344127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93394 (p : Pattern) (ha : d333467 p = 1) (hb : d338652 p = 1) : d344133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d333462 q = 1) (hb : d338652 q = 1) : d344128 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d333462, d344128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93393 q ha hb
    | true =>
      simp only [d333462, d344128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d333463 q = 1) (hb : d338652 q = 1) : d344129 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d333463, d344129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333463, d344129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d333464 q = 1) (hb : d338652 q = 1) : d344130 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d333464, d344130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333464, d344130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d333465 q = 1) (hb : d338652 q = 1) : d344131 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d333465, d344131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333465, d344131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d333466 q = 1) (hb : d338652 q = 1) : d344132 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d333466, d344132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333466, d344132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d333467 q = 1) (hb : d338652 q = 1) : d344133 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d333467, d344133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333467, d344133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93395 (p : Pattern) (ha : d333473 p = 1) (hb : d338652 p = 1) : d344139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d333468 q = 1) (hb : d338652 q = 1) : d344134 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d333468, d344134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93394 q ha hb
    | true =>
      simp only [d333468, d344134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d333469 q = 1) (hb : d338652 q = 1) : d344135 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d333469, d344135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333469, d344135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d333470 q = 1) (hb : d338652 q = 1) : d344136 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d333470, d344136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333470, d344136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d333471 q = 1) (hb : d338652 q = 1) : d344137 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d333471, d344137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333471, d344137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d333472 q = 1) (hb : d338652 q = 1) : d344138 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d333472, d344138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333472, d344138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d333473 q = 1) (hb : d338652 q = 1) : d344139 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d333473, d344139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333473, d344139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93396 (p : Pattern) (ha : d341234 p = 1) (hb : d342794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341195 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d341229 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341117 q = 1) (hb : d342732 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341117, d342732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93136 q ha hb
    | true =>
      simp only [d341117, d342732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341230 q = 1) (hb : d342790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341230, d342790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d341230, d342790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341118 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341231 q = 1) (hb : d342791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341231, d342791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341231, d342791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341232 q = 1) (hb : d342792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341232, d342792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341232, d342792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341233 q = 1) (hb : d342793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341233, d342793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341233, d342793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341234 q = 1) (hb : d342794 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341234, d342794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341234, d342794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93397 (p : Pattern) (ha : d341250 p = 1) (hb : d342801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341195 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341201 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341117 q = 1) (hb : d342732 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341117, d342732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93136 q ha hb
    | true =>
      simp only [d341117, d342732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d341230 q = 1) (hb : d342790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341230, d342790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341230, d342790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341118 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341231 q = 1) (hb : d342791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341231, d342791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341231, d342791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341232 q = 1) (hb : d342792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341232, d342792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341232, d342792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341233 q = 1) (hb : d342793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341233, d342793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341233, d342793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d341239 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d341243 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d341245 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d341124 q = 1) (hb : d342739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341124, d342739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93138 q ha hb
    | true =>
      simp only [d341124, d342739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d341246 q = 1) (hb : d342797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341246, d342797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d341246, d342797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d341125 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d341247 q = 1) (hb : d342798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341247, d342798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341247, d342798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d341248 q = 1) (hb : d342799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341248, d342799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d341248, d342799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d341249 q = 1) (hb : d342800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341249, d342800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341249, d342800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d341250 q = 1) (hb : d342801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341250, d342801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341250, d342801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93398 (p : Pattern) (ha : d341259 p = 1) (hb : d343021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341245 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341124 q = 1) (hb : d342739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341124, d342739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93138 q ha hb
    | true =>
      simp only [d341124, d342739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341246 q = 1) (hb : d342797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341246, d342797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341246, d342797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341125 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341247 q = 1) (hb : d342798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341247, d342798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341247, d342798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341257 q = 1) (hb : d342799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341257, d342799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341257, d342799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341258 q = 1) (hb : d342800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341258, d342800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341258, d342800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341259 q = 1) (hb : d343021 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341259, d343021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341259, d343021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93399 (p : Pattern) (ha : d341288 p = 1) (hb : d343067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341283 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341158 q = 1) (hb : d342773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341158, d342773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93143 q ha hb
    | true =>
      simp only [d341158, d342773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341284 q = 1) (hb : d343063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341284, d343063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341284, d343063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341159 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341285 q = 1) (hb : d343064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341285, d343064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341285, d343064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341286 q = 1) (hb : d343065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341286, d343065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341286, d343065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341287 q = 1) (hb : d343066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341287, d343066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341287, d343066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341288 q = 1) (hb : d343067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341288, d343067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341288, d343067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93400 (p : Pattern) (ha : d341294 p = 1) (hb : d343976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341251 q = 1) (hb : d342802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341251, d342802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93396 q ha hb
    | true =>
      simp only [d341251, d342802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93397 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341254 q = 1) (hb : d342803 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341254, d342803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341254, d342803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341255 q = 1) (hb : d343966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341255, d343966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341255, d343966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341256 q = 1) (hb : d343967 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341256, d343967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341256, d343967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341260 q = 1) (hb : d343022 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341260, d343022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341260, d343022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93398 q ha hb
  have h8 (q : Pattern) (ha : d341261 q = 1) (hb : d343968 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341261, d343968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341261, d343968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d341262 q = 1) (hb : d343969 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341262, d343969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341262, d343969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d341263 q = 1) (hb : d343970 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341263, d343970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341263, d343970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d341264 q = 1) (hb : d343971 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341264, d343971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341264, d343971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341289 q = 1) (hb : d343068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341289, d343068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341289, d343068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93399 q ha hb
  have h13 (q : Pattern) (ha : d341290 q = 1) (hb : d343972 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341290, d343972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341290, d343972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d341291 q = 1) (hb : d343973 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341291, d343973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341291, d343973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d341292 q = 1) (hb : d343974 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341292, d343974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341292, d343974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d341293 q = 1) (hb : d343975 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341293, d343975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341293, d343975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d341294 q = 1) (hb : d343976 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d341294, d343976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341294, d343976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro93401 (p : Pattern) (ha : d341300 p = 1) (hb : d343982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341174 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341295 q = 1) (hb : d343977 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d341295, d343977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341295, d343977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93400 q ha hb
  have h3 (q : Pattern) (ha : d341296 q = 1) (hb : d343978 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d341296, d343978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341296, d343978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341297 q = 1) (hb : d343979 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d341297, d343979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341297, d343979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341298 q = 1) (hb : d343980 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d341298, d343980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341298, d343980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341299 q = 1) (hb : d343981 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d341299, d343981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341299, d343981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341300 q = 1) (hb : d343982 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d341300, d343982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341300, d343982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93402 (p : Pattern) (ha : d341378 p = 1) (hb : d342919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341327 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d341367 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341229 q = 1) (hb : d342843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341229, d342843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93154 q ha hb
    | true =>
      simp only [d341229, d342843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93136 q ha hb
  have h5 (q : Pattern) (ha : d341368 q = 1) (hb : d342915 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341368, d342915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d341368, d342915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341374 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341375 q = 1) (hb : d342916 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341375, d342916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341375, d342916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341376 q = 1) (hb : d342917 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341376, d342917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341376, d342917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341377 q = 1) (hb : d342918 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341377, d342918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341377, d342918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341378 q = 1) (hb : d342919 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341378, d342919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341378, d342919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93403 (p : Pattern) (ha : d341397 p = 1) (hb : d342926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341327 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341367 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341229 q = 1) (hb : d342843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341229, d342843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93154 q ha hb
    | true =>
      simp only [d341229, d342843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93136 q ha hb
  have h4 (q : Pattern) (ha : d341368 q = 1) (hb : d342915 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341368, d342915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341368, d342915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d341374 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d341375 q = 1) (hb : d342916 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341375, d342916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341375, d342916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d341376 q = 1) (hb : d342917 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341376, d342917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341376, d342917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341377 q = 1) (hb : d342918 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341377, d342918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341377, d342918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d341383 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d341387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d341389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d341245 q = 1) (hb : d342859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341245, d342859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93158 q ha hb
    | true =>
      simp only [d341245, d342859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93138 q ha hb
  have h13 (q : Pattern) (ha : d341390 q = 1) (hb : d342922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341390, d342922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d341390, d342922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d341394 q = 1) (hb : d342923 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341394, d342923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341394, d342923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d341395 q = 1) (hb : d342924 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341395, d342924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341395, d342924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341396 q = 1) (hb : d342925 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341396, d342925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d341396, d342925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d341397 q = 1) (hb : d342926 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341397, d342926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341397, d342926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93404 (p : Pattern) (ha : d341406 p = 1) (hb : d343985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341245 q = 1) (hb : d342859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341245, d342859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93158 q ha hb
    | true =>
      simp only [d341245, d342859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93138 q ha hb
  have h3 (q : Pattern) (ha : d341390 q = 1) (hb : d342922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341390, d342922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341390, d342922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341394 q = 1) (hb : d342923 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341394, d342923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341394, d342923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341404 q = 1) (hb : d342924 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341404, d342924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341404, d342924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341405 q = 1) (hb : d342925 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341405, d342925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341405, d342925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341406 q = 1) (hb : d343985 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341406, d343985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341406, d343985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93405 (p : Pattern) (ha : d341448 p = 1) (hb : d343995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341283 q = 1) (hb : d342897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341283, d342897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93164 q ha hb
    | true =>
      simp only [d341283, d342897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93143 q ha hb
  have h3 (q : Pattern) (ha : d341438 q = 1) (hb : d343991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341438, d343991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341438, d343991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341445 q = 1) (hb : d343992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341445, d343992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341445, d343992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341446 q = 1) (hb : d343993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341446, d343993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341446, d343993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341447 q = 1) (hb : d343994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341447, d343994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341447, d343994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341448 q = 1) (hb : d343995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341448, d343995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341448, d343995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93406 (p : Pattern) (ha : d341460 p = 1) (hb : d344001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341398 q = 1) (hb : d342927 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341398, d342927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93402 q ha hb
    | true =>
      simp only [d341398, d342927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93403 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341401 q = 1) (hb : d342928 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341401, d342928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341401, d342928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341402 q = 1) (hb : d343983 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341402, d343983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341402, d343983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341403 q = 1) (hb : d343984 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341403, d343984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341403, d343984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341407 q = 1) (hb : d343986 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341407, d343986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341407, d343986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93404 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d341409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d341410 q = 1) (hb : d343987 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341410, d343987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341410, d343987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d341411 q = 1) (hb : d343988 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341411, d343988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341411, d343988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d341412 q = 1) (hb : d343989 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341412, d343989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341412, d343989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d341413 q = 1) (hb : d343990 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341413, d343990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341413, d343990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d341449 q = 1) (hb : d343996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341449, d343996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341449, d343996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93405 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d341456 q = 1) (hb : d343997 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341456, d343997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341456, d343997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d341457 q = 1) (hb : d343998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341457, d343998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341457, d343998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d341458 q = 1) (hb : d343999 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341458, d343999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341458, d343999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d341459 q = 1) (hb : d344000 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341459, d344000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d341459, d344000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d341460 q = 1) (hb : d344001 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d341460, d344001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341460, d344001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93407 (p : Pattern) (ha : d341466 p = 1) (hb : d344007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341461 q = 1) (hb : d344002 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d341461, d344002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341461, d344002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93406 q ha hb
  have h2 (q : Pattern) (ha : d341462 q = 1) (hb : d344003 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d341462, d344003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341462, d344003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341463 q = 1) (hb : d344004 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d341463, d344004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341463, d344004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341464 q = 1) (hb : d344005 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d341464, d344005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341464, d344005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341465 q = 1) (hb : d344006 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d341465, d344006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341465, d344006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341466 q = 1) (hb : d344007 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d341466, d344007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341466, d344007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93408 (p : Pattern) (ha : d341588 p = 1) (hb : d343103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341511 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d341577 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341485 q = 1) (hb : d343098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341485, d343098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93199 q ha hb
    | true =>
      simp only [d341485, d343098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93200 q ha hb
  have h5 (q : Pattern) (ha : d341578 q = 1) (hb : d343099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341578, d343099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d341578, d343099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341584 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341585 q = 1) (hb : d343100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341585, d343100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341585, d343100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341586 q = 1) (hb : d343101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341586, d343101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341586, d343101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341587 q = 1) (hb : d343102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341587, d343102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341587, d343102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341588 q = 1) (hb : d343103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341588, d343103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341588, d343103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93409 (p : Pattern) (ha : d341609 p = 1) (hb : d343113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341511 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341520 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341485 q = 1) (hb : d343098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341485, d343098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93199 q ha hb
    | true =>
      simp only [d341485, d343098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93200 q ha hb
  have h4 (q : Pattern) (ha : d341578 q = 1) (hb : d343099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341578, d343099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341578, d343099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d341584 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d341585 q = 1) (hb : d343100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341585, d343100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341585, d343100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d341586 q = 1) (hb : d343101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341586, d343101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341586, d343101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341587 q = 1) (hb : d343102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341587, d343102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341587, d343102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d341594 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d341599 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d341601 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d341495 q = 1) (hb : d343108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341495, d343108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93202 q ha hb
    | true =>
      simp only [d341495, d343108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93203 q ha hb
  have h13 (q : Pattern) (ha : d341602 q = 1) (hb : d343109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341602, d343109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d341602, d343109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341605 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d341606 q = 1) (hb : d343110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341606, d343110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341606, d343110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d341607 q = 1) (hb : d343111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341607, d343111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341607, d343111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341608 q = 1) (hb : d343112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341608, d343112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d341608, d343112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d341609 q = 1) (hb : d343113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341609, d343113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341609, d343113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93410 (p : Pattern) (ha : d341629 p = 1) (hb : d344011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341601 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341495 q = 1) (hb : d343108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341495, d343108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93202 q ha hb
    | true =>
      simp only [d341495, d343108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93203 q ha hb
  have h3 (q : Pattern) (ha : d341602 q = 1) (hb : d343109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341602, d343109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341602, d343109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341605 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341606 q = 1) (hb : d343110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341606, d343110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341606, d343110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341627 q = 1) (hb : d343111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341627, d343111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341627, d343111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341628 q = 1) (hb : d343112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341628, d343112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341628, d343112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341629 q = 1) (hb : d344011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341629, d344011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341629, d344011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93411 (p : Pattern) (ha : d341697 p = 1) (hb : d344022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341681 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341686 q = 1) (hb : d344017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341686, d344017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93238 q ha hb
    | true =>
      simp only [d341686, d344017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93241 q ha hb
  have h3 (q : Pattern) (ha : d341687 q = 1) (hb : d344018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341687, d344018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341687, d344018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341693 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341694 q = 1) (hb : d344019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341694, d344019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341694, d344019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341695 q = 1) (hb : d344020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341695, d344020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341695, d344020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341696 q = 1) (hb : d344021 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341696, d344021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341696, d344021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341697 q = 1) (hb : d344022 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341697, d344022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341697, d344022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93412 (p : Pattern) (ha : d341710 p = 1) (hb : d344028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341503 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341610 q = 1) (hb : d343114 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341610, d343114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93408 q ha hb
    | true =>
      simp only [d341610, d343114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93409 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341623 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341624 q = 1) (hb : d343115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341624, d343115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341624, d343115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341625 q = 1) (hb : d344009 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341625, d344009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341625, d344009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341626 q = 1) (hb : d344010 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341626, d344010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341626, d344010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341630 q = 1) (hb : d344012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341630, d344012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341630, d344012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93410 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d341632 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d341633 q = 1) (hb : d344013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341633, d344013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341633, d344013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d341634 q = 1) (hb : d344014 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341634, d344014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341634, d344014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d341635 q = 1) (hb : d344015 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341635, d344015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341635, d344015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d341636 q = 1) (hb : d344016 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341636, d344016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341636, d344016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d341698 q = 1) (hb : d344023 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341698, d344023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341698, d344023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93411 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341705 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d341706 q = 1) (hb : d344024 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341706, d344024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341706, d344024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d341707 q = 1) (hb : d344025 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341707, d344025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341707, d344025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d341708 q = 1) (hb : d344026 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341708, d344026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341708, d344026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d341709 q = 1) (hb : d344027 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341709, d344027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d341709, d344027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d341710 q = 1) (hb : d344028 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d341710, d344028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341710, d344028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93413 (p : Pattern) (ha : d341716 p = 1) (hb : d344034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341711 q = 1) (hb : d344029 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d341711, d344029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341711, d344029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93412 q ha hb
  have h2 (q : Pattern) (ha : d341712 q = 1) (hb : d344030 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d341712, d344030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341712, d344030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341713 q = 1) (hb : d344031 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d341713, d344031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341713, d344031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341714 q = 1) (hb : d344032 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d341714, d344032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341714, d344032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341715 q = 1) (hb : d344033 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d341715, d344033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341715, d344033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341716 q = 1) (hb : d344034 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d341716, d344034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341716, d344034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93414 (p : Pattern) (ha : d341846 p = 1) (hb : d343368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d341835 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341754 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
    | true =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
  have h5 (q : Pattern) (ha : d341836 q = 1) (hb : d343364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341836, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d341836, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341842 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341843 q = 1) (hb : d343365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341843, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341843, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341844 q = 1) (hb : d343366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341844, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341844, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341845 q = 1) (hb : d343367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341845, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341845, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341846 q = 1) (hb : d343368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341846, d343368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341846, d343368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93415 (p : Pattern) (ha : d341867 p = 1) (hb : d343378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341780 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341754 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93251 q ha hb
    | true =>
      simp only [d341754, d343363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93252 q ha hb
  have h4 (q : Pattern) (ha : d341836 q = 1) (hb : d343364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341836, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341836, d343364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d341842 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d341843 q = 1) (hb : d343365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341843, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d341843, d343365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d341844 q = 1) (hb : d343366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341844, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341844, d343366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341845 q = 1) (hb : d343367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341845, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341845, d343367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d341852 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d341857 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d341859 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d341764 q = 1) (hb : d343373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341764, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93254 q ha hb
    | true =>
      simp only [d341764, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93255 q ha hb
  have h13 (q : Pattern) (ha : d341860 q = 1) (hb : d343374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341860, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d341860, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341863 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d341864 q = 1) (hb : d343375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341864, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341864, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d341865 q = 1) (hb : d343376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341865, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341865, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d341866 q = 1) (hb : d343377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341866, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d341866, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d341867 q = 1) (hb : d343378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341867, d343378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341867, d343378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93416 (p : Pattern) (ha : d341887 p = 1) (hb : d344039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341859 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341764 q = 1) (hb : d343373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341764, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93254 q ha hb
    | true =>
      simp only [d341764, d343373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93255 q ha hb
  have h3 (q : Pattern) (ha : d341860 q = 1) (hb : d343374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341860, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341860, d343374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341863 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341864 q = 1) (hb : d343375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341864, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341864, d343375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341885 q = 1) (hb : d343376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341885, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341885, d343376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341886 q = 1) (hb : d343377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341886, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341886, d343377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341887 q = 1) (hb : d344039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341887, d344039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341887, d344039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93417 (p : Pattern) (ha : d341972 p = 1) (hb : d344050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341961 q = 1) (hb : d344045 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341961, d344045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93291 q ha hb
    | true =>
      simp only [d341961, d344045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93294 q ha hb
  have h3 (q : Pattern) (ha : d341962 q = 1) (hb : d344046 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341962, d344046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341962, d344046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341969 q = 1) (hb : d344047 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341969, d344047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341969, d344047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341970 q = 1) (hb : d344048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341970, d344048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341970, d344048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341971 q = 1) (hb : d344049 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341971, d344049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341971, d344049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341972 q = 1) (hb : d344050 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341972, d344050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341972, d344050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93418 (p : Pattern) (ha : d341985 p = 1) (hb : d344056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341868 q = 1) (hb : d343379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341868, d343379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93414 q ha hb
    | true =>
      simp only [d341868, d343379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93415 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341882 q = 1) (hb : d343380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341882, d343380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341882, d343380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341883 q = 1) (hb : d344037 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341883, d344037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341883, d344037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341884 q = 1) (hb : d344038 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341884, d344038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341884, d344038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341888 q = 1) (hb : d344040 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341888, d344040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341888, d344040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93416 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d341890 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d341891 q = 1) (hb : d344041 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341891, d344041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341891, d344041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d341892 q = 1) (hb : d344042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341892, d344042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341892, d344042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d341893 q = 1) (hb : d344043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341893, d344043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d341893, d344043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d341894 q = 1) (hb : d344044 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341894, d344044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341894, d344044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d341973 q = 1) (hb : d344051 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341973, d344051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341973, d344051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93417 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341980 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d341981 q = 1) (hb : d344052 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341981, d344052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341981, d344052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d341982 q = 1) (hb : d344053 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341982, d344053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341982, d344053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d341983 q = 1) (hb : d344054 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341983, d344054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d341983, d344054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d341984 q = 1) (hb : d344055 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341984, d344055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d341984, d344055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d341985 q = 1) (hb : d344056 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d341985, d344056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341985, d344056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93419 (p : Pattern) (ha : d341991 p = 1) (hb : d344062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341986 q = 1) (hb : d344057 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d341986, d344057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341986, d344057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93418 q ha hb
  have h2 (q : Pattern) (ha : d341987 q = 1) (hb : d344058 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d341987, d344058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341987, d344058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341988 q = 1) (hb : d344059 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d341988, d344059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341988, d344059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341989 q = 1) (hb : d344060 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d341989, d344060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341989, d344060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341990 q = 1) (hb : d344061 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d341990, d344061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341990, d344061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341991 q = 1) (hb : d344062 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d341991, d344062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341991, d344062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93420 (p : Pattern) (ha : d342152 p = 1) (hb : d343686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d342099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d342141 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d342073 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
    | true =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
  have h5 (q : Pattern) (ha : d342142 q = 1) (hb : d343682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342142, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d342142, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d342148 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d342149 q = 1) (hb : d343683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342149, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342149, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d342150 q = 1) (hb : d343684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342150, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d342150, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342151 q = 1) (hb : d343685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342151, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342151, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342152 q = 1) (hb : d343686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342152, d343686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342152, d343686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93421 (p : Pattern) (ha : d342173 p = 1) (hb : d343696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d342099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d342108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342073 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93310 q ha hb
    | true =>
      simp only [d342073, d343681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93311 q ha hb
  have h4 (q : Pattern) (ha : d342142 q = 1) (hb : d343682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342142, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d342142, d343682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d342148 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d342149 q = 1) (hb : d343683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342149, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342149, d343683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d342150 q = 1) (hb : d343684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342150, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342150, d343684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342151 q = 1) (hb : d343685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342151, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342151, d343685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d342158 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d342163 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d342165 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d342083 q = 1) (hb : d343691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342083, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93313 q ha hb
    | true =>
      simp only [d342083, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93314 q ha hb
  have h13 (q : Pattern) (ha : d342166 q = 1) (hb : d343692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342166, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d342166, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d342169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d342170 q = 1) (hb : d343693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342170, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342170, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d342171 q = 1) (hb : d343694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342171, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d342171, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342172 q = 1) (hb : d343695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342172, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d342172, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d342173 q = 1) (hb : d343696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342173, d343696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342173, d343696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93422 (p : Pattern) (ha : d342193 p = 1) (hb : d344068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d342165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d342083 q = 1) (hb : d343691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342083, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93313 q ha hb
    | true =>
      simp only [d342083, d343691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93314 q ha hb
  have h3 (q : Pattern) (ha : d342166 q = 1) (hb : d343692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342166, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342166, d343692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d342169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342170 q = 1) (hb : d343693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342170, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342170, d343693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d342191 q = 1) (hb : d343694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342191, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342191, d343694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342192 q = 1) (hb : d343695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342192, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342192, d343695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342193 q = 1) (hb : d344068 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342193, d344068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342193, d344068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93423 (p : Pattern) (ha : d342291 p = 1) (hb : d344079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d342275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d342280 q = 1) (hb : d344074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d342280, d344074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93348 q ha hb
    | true =>
      simp only [d342280, d344074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93351 q ha hb
  have h3 (q : Pattern) (ha : d342281 q = 1) (hb : d344075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342281, d344075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342281, d344075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d342287 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342288 q = 1) (hb : d344076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342288, d344076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342288, d344076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d342289 q = 1) (hb : d344077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342289, d344077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342289, d344077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342290 q = 1) (hb : d344078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342290, d344078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342290, d344078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342291 q = 1) (hb : d344079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342291, d344079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342291, d344079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93424 (p : Pattern) (ha : d342304 p = 1) (hb : d344085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d342091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342174 q = 1) (hb : d343697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342174, d343697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93420 q ha hb
    | true =>
      simp only [d342174, d343697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93421 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342187 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342188 q = 1) (hb : d343698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342188, d343698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342188, d343698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342189 q = 1) (hb : d344066 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342189, d344066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342189, d344066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d342190 q = 1) (hb : d344067 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d342190, d344067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342190, d344067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342194 q = 1) (hb : d344069 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342194, d344069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d342194, d344069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93422 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d342196 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d342197 q = 1) (hb : d344070 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342197, d344070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d342197, d344070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d342198 q = 1) (hb : d344071 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342198, d344071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342198, d344071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d342199 q = 1) (hb : d344072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d342199, d344072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342199, d344072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d342200 q = 1) (hb : d344073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d342200, d344073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342200, d344073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d342292 q = 1) (hb : d344080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342292, d344080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d342292, d344080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93423 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d342299 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d342300 q = 1) (hb : d344081 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342300, d344081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342300, d344081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d342301 q = 1) (hb : d344082 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d342301, d344082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d342301, d344082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d342302 q = 1) (hb : d344083 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d342302, d344083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d342302, d344083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d342303 q = 1) (hb : d344084 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d342303, d344084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d342303, d344084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d342304 q = 1) (hb : d344085 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d342304, d344085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342304, d344085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93425 (p : Pattern) (ha : d342310 p = 1) (hb : d344091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342305 q = 1) (hb : d344086 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d342305, d344086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342305, d344086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93424 q ha hb
  have h2 (q : Pattern) (ha : d342306 q = 1) (hb : d344087 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d342306, d344087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342306, d344087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d342307 q = 1) (hb : d344088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d342307, d344088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342307, d344088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d342308 q = 1) (hb : d344089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d342308, d344089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342308, d344089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d342309 q = 1) (hb : d344090 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d342309, d344090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342309, d344090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342310 q = 1) (hb : d344091 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d342310, d344091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d342310, d344091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93426 (p : Pattern) (ha : d342665 p = 1) (hb : d344097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d341467 q = 1) (hb : d344008 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d341467, d344008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93401 q ha hb
    | true =>
      simp only [d341467, d344008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93407 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341717 q = 1) (hb : d344035 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d341717, d344035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341717, d344035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93413 q ha hb
  have h3 (q : Pattern) (ha : d341718 q = 1) (hb : d344036 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d341718, d344036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d341718, d344036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341992 q = 1) (hb : d344063 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d341992, d344063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341992, d344063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93419 q ha hb
  have h5 (q : Pattern) (ha : d341993 q = 1) (hb : d344064 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d341993, d344064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341993, d344064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341994 q = 1) (hb : d344065 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d341994, d344065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341994, d344065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342311 q = 1) (hb : d344092 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d342311, d344092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342311, d344092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93425 q ha hb
  have h8 (q : Pattern) (ha : d342312 q = 1) (hb : d344093 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d342312, d344093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342312, d344093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342313 q = 1) (hb : d344094 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d342313, d344094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d342313, d344094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342314 q = 1) (hb : d344095 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d342314, d344095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d342314, d344095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d342663 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d342664 q = 1) (hb : d344096 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d342664, d344096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342664, d344096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d342665 q = 1) (hb : d344097 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d342665, d344097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d342665, d344097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro93427 (p : Pattern) (ha : d342671 p = 1) (hb : d344103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342666 q = 1) (hb : d344098 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d342666, d344098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93426 q ha hb
    | true =>
      simp only [d342666, d344098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342667 q = 1) (hb : d344099 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d342667, d344099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342667, d344099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342668 q = 1) (hb : d344100 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d342668, d344100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342668, d344100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342669 q = 1) (hb : d344101 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d342669, d344101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342669, d344101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342670 q = 1) (hb : d344102 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d342670, d344102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342670, d344102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342671 q = 1) (hb : d344103 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d342671, d344103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342671, d344103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93428 (p : Pattern) (ha : d342677 p = 1) (hb : d344109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342672 q = 1) (hb : d344104 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d342672, d344104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93427 q ha hb
    | true =>
      simp only [d342672, d344104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342673 q = 1) (hb : d344105 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d342673, d344105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342673, d344105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342674 q = 1) (hb : d344106 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d342674, d344106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342674, d344106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342675 q = 1) (hb : d344107 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d342675, d344107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342675, d344107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342676 q = 1) (hb : d344108 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d342676, d344108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342676, d344108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342677 q = 1) (hb : d344109 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d342677, d344109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342677, d344109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93429 (p : Pattern) (ha : d342683 p = 1) (hb : d344115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342678 q = 1) (hb : d344110 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d342678, d344110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93428 q ha hb
    | true =>
      simp only [d342678, d344110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342679 q = 1) (hb : d344111 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d342679, d344111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342679, d344111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342680 q = 1) (hb : d344112 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d342680, d344112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342680, d344112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342681 q = 1) (hb : d344113 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d342681, d344113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342681, d344113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342682 q = 1) (hb : d344114 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d342682, d344114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342682, d344114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342683 q = 1) (hb : d344115 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d342683, d344115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342683, d344115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93430 (p : Pattern) (ha : d342689 p = 1) (hb : d344121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342684 q = 1) (hb : d344116 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d342684, d344116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93429 q ha hb
    | true =>
      simp only [d342684, d344116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342685 q = 1) (hb : d344117 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d342685, d344117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342685, d344117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342686 q = 1) (hb : d344118 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d342686, d344118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342686, d344118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342687 q = 1) (hb : d344119 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d342687, d344119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342687, d344119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342688 q = 1) (hb : d344120 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d342688, d344120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342688, d344120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342689 q = 1) (hb : d344121 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d342689, d344121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342689, d344121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93431 (p : Pattern) (ha : d342695 p = 1) (hb : d344127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342690 q = 1) (hb : d344122 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d342690, d344122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93430 q ha hb
    | true =>
      simp only [d342690, d344122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342691 q = 1) (hb : d344123 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d342691, d344123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342691, d344123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342692 q = 1) (hb : d344124 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d342692, d344124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342692, d344124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342693 q = 1) (hb : d344125 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d342693, d344125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342693, d344125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342694 q = 1) (hb : d344126 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d342694, d344126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342694, d344126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342695 q = 1) (hb : d344127 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d342695, d344127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342695, d344127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93432 (p : Pattern) (ha : d342701 p = 1) (hb : d344133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342696 q = 1) (hb : d344128 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d342696, d344128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93431 q ha hb
    | true =>
      simp only [d342696, d344128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342697 q = 1) (hb : d344129 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d342697, d344129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342697, d344129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342698 q = 1) (hb : d344130 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d342698, d344130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342698, d344130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342699 q = 1) (hb : d344131 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d342699, d344131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342699, d344131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342700 q = 1) (hb : d344132 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d342700, d344132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342700, d344132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342701 q = 1) (hb : d344133 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d342701, d344133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342701, d344133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93433 (p : Pattern) (ha : d342707 p = 1) (hb : d344139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342702 q = 1) (hb : d344134 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d342702, d344134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93432 q ha hb
    | true =>
      simp only [d342702, d344134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d342703 q = 1) (hb : d344135 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d342703, d344135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342703, d344135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d342704 q = 1) (hb : d344136 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d342704, d344136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342704, d344136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d342705 q = 1) (hb : d344137 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d342705, d344137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342705, d344137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d342706 q = 1) (hb : d344138 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d342706, d344138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342706, d344138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d342707 q = 1) (hb : d344139 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d342707, d344139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342707, d344139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro93434 (p : Pattern) (ha : d342794 p = 1) (hb : d344144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d338988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d338994 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d339022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d342732 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342790 q = 1) (hb : d344140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342790, d344140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342790, d344140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d338911 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d342791 q = 1) (hb : d344141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342791, d344141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342791, d344141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342792 q = 1) (hb : d344142 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342792, d344142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342792, d344142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342793 q = 1) (hb : d344143 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342793, d344143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342793, d344143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342794 q = 1) (hb : d344144 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342794, d344144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342794, d344144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93435 (p : Pattern) (ha : d342801 p = 1) (hb : d344149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d338994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d342732 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d342790 q = 1) (hb : d344140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342790, d344140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342790, d344140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d338911 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d342791 q = 1) (hb : d344141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342791, d344141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342791, d344141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342792 q = 1) (hb : d344142 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342792, d344142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342792, d344142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342793 q = 1) (hb : d344143 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342793, d344143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342793, d344143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d339060 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d339064 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d339066 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d342739 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d342797 q = 1) (hb : d344145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342797, d344145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342797, d344145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d338918 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d342798 q = 1) (hb : d344146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342798, d344146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342798, d344146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342799 q = 1) (hb : d344147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342799, d344147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342799, d344147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342800 q = 1) (hb : d344148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342800, d344148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342800, d344148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d342801 q = 1) (hb : d344149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342801, d344149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342801, d344149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93436 (p : Pattern) (ha : d343021 p = 1) (hb : d344156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342797 q = 1) (hb : d344145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342797, d344145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342797, d344145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d338918 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342798 q = 1) (hb : d344146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342798, d344146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342798, d344146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342799 q = 1) (hb : d344154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342799, d344154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342799, d344154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342800 q = 1) (hb : d344155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342800, d344155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342800, d344155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343021 q = 1) (hb : d344156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343021, d344156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343021, d344156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93437 (p : Pattern) (ha : d343067 p = 1) (hb : d344166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343063 q = 1) (hb : d344162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343063, d344162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343063, d344162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d338952 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343064 q = 1) (hb : d344163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343064, d344163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343064, d344163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343065 q = 1) (hb : d344164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343065, d344164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343065, d344164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343066 q = 1) (hb : d344165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343066, d344165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343066, d344165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343067 q = 1) (hb : d344166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343067, d344166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343067, d344166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93438 (p : Pattern) (ha : d343976 p = 1) (hb : d344172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342802 q = 1) (hb : d344150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342802, d344150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93434 q ha hb
    | true =>
      simp only [d342802, d344150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93435 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342803 q = 1) (hb : d344151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342803, d344151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342803, d344151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343966 q = 1) (hb : d344152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d343966, d344152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343966, d344152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343967 q = 1) (hb : d344153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d343967, d344153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343967, d344153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343022 q = 1) (hb : d344157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343022, d344157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343022, d344157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93436 q ha hb
  have h8 (q : Pattern) (ha : d343968 q = 1) (hb : d344158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343968, d344158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d343968, d344158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d343969 q = 1) (hb : d344159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d343969, d344159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d343969, d344159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d343970 q = 1) (hb : d344160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d343970, d344160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d343970, d344160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d343971 q = 1) (hb : d344161 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d343971, d344161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d343971, d344161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d343068 q = 1) (hb : d344167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343068, d344167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343068, d344167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93437 q ha hb
  have h13 (q : Pattern) (ha : d343972 q = 1) (hb : d344168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343972, d344168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d343972, d344168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d343973 q = 1) (hb : d344169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d343973, d344169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d343973, d344169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d343974 q = 1) (hb : d344170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d343974, d344170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d343974, d344170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d343975 q = 1) (hb : d344171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d343975, d344171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d343975, d344171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d343976 q = 1) (hb : d344172 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d343976, d344172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d343976, d344172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro93439 (p : Pattern) (ha : d343982 p = 1) (hb : d344178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338967 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d343977 q = 1) (hb : d344173 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d343977, d344173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343977, d344173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93438 q ha hb
  have h3 (q : Pattern) (ha : d343978 q = 1) (hb : d344174 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d343978, d344174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343978, d344174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d343979 q = 1) (hb : d344175 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d343979, d344175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343979, d344175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d343980 q = 1) (hb : d344176 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d343980, d344176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343980, d344176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343981 q = 1) (hb : d344177 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d343981, d344177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343981, d344177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343982 q = 1) (hb : d344178 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d343982, d344178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343982, d344178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93440 (p : Pattern) (ha : d342919 p = 1) (hb : d344183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339169 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d339209 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d342843 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342915 q = 1) (hb : d344179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342915, d344179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342915, d344179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d339244 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d342916 q = 1) (hb : d344180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342916, d344180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d342916, d344180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342917 q = 1) (hb : d344181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342917, d344181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342917, d344181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d342918 q = 1) (hb : d344182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342918, d344182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342918, d344182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d342919 q = 1) (hb : d344183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342919, d344183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342919, d344183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93441 (p : Pattern) (ha : d342926 p = 1) (hb : d344188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339163 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d342843 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d342915 q = 1) (hb : d344179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342915, d344179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d342915, d344179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d339244 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d342916 q = 1) (hb : d344180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342916, d344180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d342916, d344180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342917 q = 1) (hb : d344181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342917, d344181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342917, d344181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d342918 q = 1) (hb : d344182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342918, d344182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342918, d344182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d339253 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d339257 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d339259 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d342859 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d342922 q = 1) (hb : d344184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342922, d344184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d342922, d344184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339265 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d342923 q = 1) (hb : d344185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342923, d344185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d342923, d344185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d342924 q = 1) (hb : d344186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342924, d344186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d342924, d344186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d342925 q = 1) (hb : d344187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342925, d344187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d342925, d344187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d342926 q = 1) (hb : d344188 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d342926, d344188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d342926, d344188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93442 (p : Pattern) (ha : d343985 p = 1) (hb : d344195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339259 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342922 q = 1) (hb : d344184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d342922, d344184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342922, d344184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339265 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d342923 q = 1) (hb : d344185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d342923, d344185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d342923, d344185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d342924 q = 1) (hb : d344193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d342924, d344193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342924, d344193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d342925 q = 1) (hb : d344194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d342925, d344194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d342925, d344194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343985 q = 1) (hb : d344195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343985, d344195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343985, d344195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93443 (p : Pattern) (ha : d343995 p = 1) (hb : d344205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d342897 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343991 q = 1) (hb : d344201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343991, d344201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343991, d344201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343992 q = 1) (hb : d344202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343992, d344202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343992, d344202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343993 q = 1) (hb : d344203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343993, d344203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343993, d344203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343994 q = 1) (hb : d344204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343994, d344204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343994, d344204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343995 q = 1) (hb : d344205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343995, d344205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343995, d344205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93444 (p : Pattern) (ha : d344001 p = 1) (hb : d344211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339157 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d342927 q = 1) (hb : d344189 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d342927, d344189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93440 q ha hb
    | true =>
      simp only [d342927, d344189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93441 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339272 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d342928 q = 1) (hb : d344190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d342928, d344190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d342928, d344190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343983 q = 1) (hb : d344191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d343983, d344191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343983, d344191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343984 q = 1) (hb : d344192 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d343984, d344192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343984, d344192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343986 q = 1) (hb : d344196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343986, d344196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343986, d344196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93442 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d339281 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d343987 q = 1) (hb : d344197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343987, d344197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d343987, d344197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d343988 q = 1) (hb : d344198 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d343988, d344198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d343988, d344198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d343989 q = 1) (hb : d344199 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d343989, d344199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d343989, d344199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d343990 q = 1) (hb : d344200 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d343990, d344200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d343990, d344200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d343996 q = 1) (hb : d344206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343996, d344206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343996, d344206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93443 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d343997 q = 1) (hb : d344207 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343997, d344207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d343997, d344207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d343998 q = 1) (hb : d344208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d343998, d344208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d343998, d344208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d343999 q = 1) (hb : d344209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d343999, d344209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d343999, d344209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d344000 q = 1) (hb : d344210 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344000, d344210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d344000, d344210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d344001 q = 1) (hb : d344211 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d344001, d344211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d344001, d344211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93445 (p : Pattern) (ha : d344007 p = 1) (hb : d344217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344002 q = 1) (hb : d344212 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d344002, d344212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344002, d344212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93444 q ha hb
  have h2 (q : Pattern) (ha : d344003 q = 1) (hb : d344213 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d344003, d344213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344003, d344213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d344004 q = 1) (hb : d344214 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d344004, d344214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344004, d344214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d344005 q = 1) (hb : d344215 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d344005, d344215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344005, d344215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d344006 q = 1) (hb : d344216 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d344006, d344216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344006, d344216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344007 q = 1) (hb : d344217 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d344007, d344217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344007, d344217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93446 (p : Pattern) (ha : d343103 p = 1) (hb : d344223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d339468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d343098 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343099 q = 1) (hb : d344219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343099, d344219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343099, d344219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d339524 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d343100 q = 1) (hb : d344220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343100, d344220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d343100, d344220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343101 q = 1) (hb : d344221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343101, d344221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d343101, d344221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d343102 q = 1) (hb : d344222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343102, d344222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343102, d344222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d343103 q = 1) (hb : d344223 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343103, d344223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343103, d344223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93447 (p : Pattern) (ha : d343113 p = 1) (hb : d344228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339402 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339411 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d343098 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d343099 q = 1) (hb : d344219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343099, d344219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d343099, d344219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d339524 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d343100 q = 1) (hb : d344220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343100, d344220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343100, d344220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343101 q = 1) (hb : d344221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343101, d344221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343101, d344221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343102 q = 1) (hb : d344222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343102, d344222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343102, d344222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d339534 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d339539 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d339541 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d343108 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d343109 q = 1) (hb : d344224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343109, d344224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d343109, d344224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339548 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d343110 q = 1) (hb : d344225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343110, d344225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d343110, d344225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d343111 q = 1) (hb : d344226 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343111, d344226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d343111, d344226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d343112 q = 1) (hb : d344227 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343112, d344227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d343112, d344227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d343113 q = 1) (hb : d344228 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343113, d344228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d343113, d344228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93448 (p : Pattern) (ha : d344011 p = 1) (hb : d344235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339541 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d343108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343109 q = 1) (hb : d344224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343109, d344224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343109, d344224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339548 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343110 q = 1) (hb : d344225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343110, d344225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343110, d344225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343111 q = 1) (hb : d344233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343111, d344233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343111, d344233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343112 q = 1) (hb : d344234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343112, d344234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343112, d344234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344011 q = 1) (hb : d344235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344011, d344235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344011, d344235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93449 (p : Pattern) (ha : d344022 p = 1) (hb : d344245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d344017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d344018 q = 1) (hb : d344241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344018, d344241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344018, d344241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339664 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344019 q = 1) (hb : d344242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344019, d344242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344019, d344242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344020 q = 1) (hb : d344243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344020, d344243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344020, d344243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344021 q = 1) (hb : d344244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344021, d344244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344021, d344244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344022 q = 1) (hb : d344245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344022, d344245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344022, d344245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93450 (p : Pattern) (ha : d344028 p = 1) (hb : d344251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d343114 q = 1) (hb : d344229 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343114, d344229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93446 q ha hb
    | true =>
      simp only [d343114, d344229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93447 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339566 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343115 q = 1) (hb : d344230 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343115, d344230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343115, d344230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344009 q = 1) (hb : d344231 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344009, d344231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344009, d344231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344010 q = 1) (hb : d344232 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344010, d344232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344010, d344232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344012 q = 1) (hb : d344236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344012, d344236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344012, d344236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93448 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d339575 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d344013 q = 1) (hb : d344237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344013, d344237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d344013, d344237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d344014 q = 1) (hb : d344238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344014, d344238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d344014, d344238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d344015 q = 1) (hb : d344239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344015, d344239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d344015, d344239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d344016 q = 1) (hb : d344240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344016, d344240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d344016, d344240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d344023 q = 1) (hb : d344246 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344023, d344246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344023, d344246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93449 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339680 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d344024 q = 1) (hb : d344247 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344024, d344247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d344024, d344247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d344025 q = 1) (hb : d344248 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344025, d344248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d344025, d344248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d344026 q = 1) (hb : d344249 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344026, d344249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d344026, d344249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d344027 q = 1) (hb : d344250 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344027, d344250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d344027, d344250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d344028 q = 1) (hb : d344251 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d344028, d344251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d344028, d344251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93451 (p : Pattern) (ha : d344034 p = 1) (hb : d344257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344029 q = 1) (hb : d344252 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d344029, d344252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344029, d344252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93450 q ha hb
  have h2 (q : Pattern) (ha : d344030 q = 1) (hb : d344253 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d344030, d344253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344030, d344253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d344031 q = 1) (hb : d344254 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d344031, d344254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344031, d344254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d344032 q = 1) (hb : d344255 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d344032, d344255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344032, d344255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d344033 q = 1) (hb : d344256 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d344033, d344256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344033, d344256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344034 q = 1) (hb : d344257 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d344034, d344257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344034, d344257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93452 (p : Pattern) (ha : d343368 p = 1) (hb : d344264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d339810 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343364 q = 1) (hb : d344260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343364, d344260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343364, d344260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d339891 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d343365 q = 1) (hb : d344261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343365, d344261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d343365, d344261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343366 q = 1) (hb : d344262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343366, d344262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d343366, d344262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d343367 q = 1) (hb : d344263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343367, d344263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343367, d344263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d343368 q = 1) (hb : d344264 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343368, d344264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343368, d344264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93453 (p : Pattern) (ha : d343378 p = 1) (hb : d344269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339810 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d343363 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d343364 q = 1) (hb : d344260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343364, d344260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d343364, d344260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d339891 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d343365 q = 1) (hb : d344261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343365, d344261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343365, d344261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343366 q = 1) (hb : d344262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343366, d344262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343366, d344262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343367 q = 1) (hb : d344263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343367, d344263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343367, d344263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d339901 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d339906 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d339908 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d343373 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d343374 q = 1) (hb : d344265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343374, d344265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d343374, d344265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339915 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d343375 q = 1) (hb : d344266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343375, d344266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d343375, d344266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d343376 q = 1) (hb : d344267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343376, d344267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d343376, d344267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d343377 q = 1) (hb : d344268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343377, d344268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d343377, d344268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d343378 q = 1) (hb : d344269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343378, d344269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d343378, d344269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93454 (p : Pattern) (ha : d344039 p = 1) (hb : d344276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d343373 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343374 q = 1) (hb : d344265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343374, d344265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343374, d344265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339915 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343375 q = 1) (hb : d344266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343375, d344266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343375, d344266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343376 q = 1) (hb : d344274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343376, d344274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343376, d344274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343377 q = 1) (hb : d344275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343377, d344275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343377, d344275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344039 q = 1) (hb : d344276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344039, d344276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344039, d344276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93455 (p : Pattern) (ha : d344050 p = 1) (hb : d344286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d340008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d344045 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d344046 q = 1) (hb : d344282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344046, d344282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344046, d344282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d340063 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344047 q = 1) (hb : d344283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344047, d344283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344047, d344283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344048 q = 1) (hb : d344284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344048, d344284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344048, d344284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344049 q = 1) (hb : d344285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344049, d344285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344049, d344285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344050 q = 1) (hb : d344286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344050, d344286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344050, d344286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93456 (p : Pattern) (ha : d344056 p = 1) (hb : d344292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d343379 q = 1) (hb : d344270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343379, d344270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93452 q ha hb
    | true =>
      simp only [d343379, d344270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93453 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343380 q = 1) (hb : d344271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343380, d344271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343380, d344271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344037 q = 1) (hb : d344272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344037, d344272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344037, d344272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344038 q = 1) (hb : d344273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344038, d344273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344038, d344273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344040 q = 1) (hb : d344277 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344040, d344277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344040, d344277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93454 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d339942 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d344041 q = 1) (hb : d344278 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344041, d344278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d344041, d344278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d344042 q = 1) (hb : d344279 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344042, d344279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d344042, d344279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d344043 q = 1) (hb : d344280 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344043, d344280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d344043, d344280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d344044 q = 1) (hb : d344281 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344044, d344281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d344044, d344281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d344051 q = 1) (hb : d344287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344051, d344287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344051, d344287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93455 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d340079 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d344052 q = 1) (hb : d344288 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344052, d344288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d344052, d344288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d344053 q = 1) (hb : d344289 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344053, d344289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d344053, d344289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d344054 q = 1) (hb : d344290 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344054, d344290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d344054, d344290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d344055 q = 1) (hb : d344291 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344055, d344291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d344055, d344291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d344056 q = 1) (hb : d344292 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d344056, d344292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d344056, d344292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93457 (p : Pattern) (ha : d344062 p = 1) (hb : d344298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344057 q = 1) (hb : d344293 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d344057, d344293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344057, d344293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93456 q ha hb
  have h2 (q : Pattern) (ha : d344058 q = 1) (hb : d344294 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d344058, d344294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344058, d344294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d344059 q = 1) (hb : d344295 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d344059, d344295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344059, d344295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d344060 q = 1) (hb : d344296 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d344060, d344296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344060, d344296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d344061 q = 1) (hb : d344297 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d344061, d344297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344061, d344297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344062 q = 1) (hb : d344298 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d344062, d344298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344062, d344298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93458 (p : Pattern) (ha : d343686 p = 1) (hb : d344306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d340198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d340207 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d340240 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343682 q = 1) (hb : d344302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343682, d344302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343682, d344302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d340330 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d343683 q = 1) (hb : d344303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343683, d344303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d343683, d344303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343684 q = 1) (hb : d344304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343684, d344304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d343684, d344304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d343685 q = 1) (hb : d344305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343685, d344305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343685, d344305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d343686 q = 1) (hb : d344306 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343686, d344306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343686, d344306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93459 (p : Pattern) (ha : d343696 p = 1) (hb : d344311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d340198 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d340207 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d340240 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d343681 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d343682 q = 1) (hb : d344302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343682, d344302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d343682, d344302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d340330 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d343683 q = 1) (hb : d344303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343683, d344303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d343683, d344303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343684 q = 1) (hb : d344304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343684, d344304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343684, d344304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d343685 q = 1) (hb : d344305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343685, d344305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343685, d344305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d340340 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d340345 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d340347 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d343691 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d343692 q = 1) (hb : d344307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343692, d344307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d343692, d344307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d340354 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d343693 q = 1) (hb : d344308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343693, d344308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d343693, d344308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d343694 q = 1) (hb : d344309 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343694, d344309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d343694, d344309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d343695 q = 1) (hb : d344310 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343695, d344310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d343695, d344310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d343696 q = 1) (hb : d344311 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d343696, d344311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d343696, d344311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro93460 (p : Pattern) (ha : d344068 p = 1) (hb : d344318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d340347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d343691 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343692 q = 1) (hb : d344307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d343692, d344307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343692, d344307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d340354 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d343693 q = 1) (hb : d344308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d343693, d344308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d343693, d344308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d343694 q = 1) (hb : d344316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d343694, d344316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343694, d344316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d343695 q = 1) (hb : d344317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d343695, d344317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d343695, d344317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344068 q = 1) (hb : d344318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344068, d344318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344068, d344318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93461 (p : Pattern) (ha : d344079 p = 1) (hb : d344328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d340460 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d344074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d344075 q = 1) (hb : d344324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344075, d344324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344075, d344324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d340519 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344076 q = 1) (hb : d344325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344076, d344325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344076, d344325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344077 q = 1) (hb : d344326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344077, d344326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344077, d344326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344078 q = 1) (hb : d344327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344078, d344327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344078, d344327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344079 q = 1) (hb : d344328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344079, d344328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344079, d344328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93462 (p : Pattern) (ha : d344085 p = 1) (hb : d344334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d340190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d343697 q = 1) (hb : d344312 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d343697, d344312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93458 q ha hb
    | true =>
      simp only [d343697, d344312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93459 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d340372 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d343698 q = 1) (hb : d344313 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d343698, d344313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d343698, d344313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344066 q = 1) (hb : d344314 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344066, d344314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344066, d344314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344067 q = 1) (hb : d344315 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344067, d344315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344067, d344315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344069 q = 1) (hb : d344319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344069, d344319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344069, d344319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93460 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d340381 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d344070 q = 1) (hb : d344320 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344070, d344320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d344070, d344320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d344071 q = 1) (hb : d344321 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344071, d344321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d344071, d344321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d344072 q = 1) (hb : d344322 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344072, d344322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d344072, d344322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d344073 q = 1) (hb : d344323 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344073, d344323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d344073, d344323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d344080 q = 1) (hb : d344329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344080, d344329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344080, d344329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93461 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d340535 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d344081 q = 1) (hb : d344330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344081, d344330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d344081, d344330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d344082 q = 1) (hb : d344331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344082, d344331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d344082, d344331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d344083 q = 1) (hb : d344332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344083, d344332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d344083, d344332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d344084 q = 1) (hb : d344333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344084, d344333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d344084, d344333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d344085 q = 1) (hb : d344334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d344085, d344334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d344085, d344334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93463 (p : Pattern) (ha : d344091 p = 1) (hb : d344340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344086 q = 1) (hb : d344335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d344086, d344335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344086, d344335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93462 q ha hb
  have h2 (q : Pattern) (ha : d344087 q = 1) (hb : d344336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d344087, d344336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344087, d344336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d344088 q = 1) (hb : d344337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d344088, d344337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344088, d344337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d344089 q = 1) (hb : d344338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d344089, d344338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344089, d344338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d344090 q = 1) (hb : d344339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d344090, d344339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344090, d344339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344091 q = 1) (hb : d344340 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d344091, d344340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344091, d344340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93464 (p : Pattern) (ha : d344097 p = 1) (hb : d344389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d344008 q = 1) (hb : d344218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d344008, d344218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93439 q ha hb
    | true =>
      simp only [d344008, d344218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93445 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d344035 q = 1) (hb : d344258 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d344035, d344258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344035, d344258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93451 q ha hb
  have h3 (q : Pattern) (ha : d344036 q = 1) (hb : d344259 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d344036, d344259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344036, d344259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d344063 q = 1) (hb : d344299 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d344063, d344299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344063, d344299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93457 q ha hb
  have h5 (q : Pattern) (ha : d344064 q = 1) (hb : d344300 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d344064, d344300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344064, d344300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344065 q = 1) (hb : d344301 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d344065, d344301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344065, d344301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344092 q = 1) (hb : d344341 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d344092, d344341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344092, d344341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93463 q ha hb
  have h8 (q : Pattern) (ha : d344093 q = 1) (hb : d344342 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d344093, d344342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344093, d344342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d344094 q = 1) (hb : d344343 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d344094, d344343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344094, d344343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d344095 q = 1) (hb : d344344 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d344095, d344344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d344095, d344344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d344387 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d344096 q = 1) (hb : d344388 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d344096, d344388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d344096, d344388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d344097 q = 1) (hb : d344389 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d344097, d344389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d344097, d344389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h13 p ha hb
theorem andIntro93465 (p : Pattern) (ha : d344103 p = 1) (hb : d344395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344098 q = 1) (hb : d344390 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d344098, d344390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93464 q ha hb
    | true =>
      simp only [d344098, d344390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344099 q = 1) (hb : d344391 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d344099, d344391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344099, d344391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344100 q = 1) (hb : d344392 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d344100, d344392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344100, d344392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344101 q = 1) (hb : d344393 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d344101, d344393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344101, d344393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344102 q = 1) (hb : d344394 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d344102, d344394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344102, d344394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344103 q = 1) (hb : d344395 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d344103, d344395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344103, d344395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93466 (p : Pattern) (ha : d344109 p = 1) (hb : d344401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344104 q = 1) (hb : d344396 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d344104, d344396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93465 q ha hb
    | true =>
      simp only [d344104, d344396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344105 q = 1) (hb : d344397 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d344105, d344397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344105, d344397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344106 q = 1) (hb : d344398 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d344106, d344398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344106, d344398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344107 q = 1) (hb : d344399 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d344107, d344399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344107, d344399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344108 q = 1) (hb : d344400 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d344108, d344400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344108, d344400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344109 q = 1) (hb : d344401 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d344109, d344401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344109, d344401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93467 (p : Pattern) (ha : d344115 p = 1) (hb : d344407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344110 q = 1) (hb : d344402 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d344110, d344402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93466 q ha hb
    | true =>
      simp only [d344110, d344402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344111 q = 1) (hb : d344403 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d344111, d344403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344111, d344403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344112 q = 1) (hb : d344404 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d344112, d344404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344112, d344404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344113 q = 1) (hb : d344405 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d344113, d344405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344113, d344405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344114 q = 1) (hb : d344406 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d344114, d344406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344114, d344406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344115 q = 1) (hb : d344407 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d344115, d344407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344115, d344407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93468 (p : Pattern) (ha : d344121 p = 1) (hb : d344413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344116 q = 1) (hb : d344408 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d344116, d344408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93467 q ha hb
    | true =>
      simp only [d344116, d344408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344117 q = 1) (hb : d344409 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d344117, d344409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344117, d344409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344118 q = 1) (hb : d344410 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d344118, d344410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344118, d344410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344119 q = 1) (hb : d344411 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d344119, d344411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344119, d344411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344120 q = 1) (hb : d344412 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d344120, d344412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344120, d344412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344121 q = 1) (hb : d344413 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d344121, d344413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344121, d344413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93469 (p : Pattern) (ha : d344127 p = 1) (hb : d344419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344122 q = 1) (hb : d344414 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d344122, d344414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93468 q ha hb
    | true =>
      simp only [d344122, d344414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344123 q = 1) (hb : d344415 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d344123, d344415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344123, d344415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344124 q = 1) (hb : d344416 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d344124, d344416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344124, d344416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344125 q = 1) (hb : d344417 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d344125, d344417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344125, d344417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344126 q = 1) (hb : d344418 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d344126, d344418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344126, d344418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344127 q = 1) (hb : d344419 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d344127, d344419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344127, d344419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93470 (p : Pattern) (ha : d344133 p = 1) (hb : d344425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344128 q = 1) (hb : d344420 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d344128, d344420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93469 q ha hb
    | true =>
      simp only [d344128, d344420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344129 q = 1) (hb : d344421 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d344129, d344421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344129, d344421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344130 q = 1) (hb : d344422 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d344130, d344422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344130, d344422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344131 q = 1) (hb : d344423 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d344131, d344423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344131, d344423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344132 q = 1) (hb : d344424 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d344132, d344424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344132, d344424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344133 q = 1) (hb : d344425 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d344133, d344425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344133, d344425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93471 (p : Pattern) (ha : d344139 p = 1) (hb : d344431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344134 q = 1) (hb : d344426 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d344134, d344426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93470 q ha hb
    | true =>
      simp only [d344134, d344426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d344135 q = 1) (hb : d344427 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d344135, d344427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344135, d344427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d344136 q = 1) (hb : d344428 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d344136, d344428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d344136, d344428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d344137 q = 1) (hb : d344429 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d344137, d344429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344137, d344429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d344138 q = 1) (hb : d344430 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d344138, d344430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344138, d344430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d344139 q = 1) (hb : d344431 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d344139, d344431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344139, d344431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro93472 (p : Pattern) (ha : d138 p = 1) (hb : d310056 p = 1) : d30638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d310056 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d310056, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d310056, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d310056 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d310056 q = 1) : d30635 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d310056 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d310056 q = 1) : d30636 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d30636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d30636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d310056 q = 1) : d30637 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d30637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d30637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d23 q = 1) (hb : d310056 q = 1) : d23 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d138 q = 1) (hb : d310056 q = 1) : d30638 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d30638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138, d30638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93473 (p : Pattern) (ha : d144 p = 1) (hb : d310056 p = 1) : d30644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d310056 q = 1) : d30639 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d30639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93472 q ha hb
    | true =>
      simp only [d139, d30639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d310056 q = 1) : d30640 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d30640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d30640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d310056 q = 1) : d30641 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d30641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d30641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d310056 q = 1) : d30642 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d30642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d30642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d310056 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d310056 q = 1) : d30643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d30643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d30643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d310056 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d310056 q = 1) : d30644 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d30644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d30644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93474 (p : Pattern) (ha : d150 p = 1) (hb : d310056 p = 1) : d30650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d310056 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d310056 q = 1) : d30645 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d30645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93473 q ha hb
    | true =>
      simp only [d145, d30645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d310056 q = 1) : d30646 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d30646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d30646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d310056 q = 1) : d30647 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d30647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d30647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d310056 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d310056 q = 1) : d30648 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d30648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d30648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d310056 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d310056 q = 1) : d30649 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d30649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d30649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d310056 q = 1) : d30650 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d30650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d30650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro93475 (p : Pattern) (ha : d203 p = 1) (hb : d310056 p = 1) : d30663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310056 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d310056 q = 1) : d30653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d310056 q = 1) : d30654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d310056 q = 1) : d30655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d30655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d30655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d310056 q = 1) : d30663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d30663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d30663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro93476 (p : Pattern) (ha : d4349 p = 1) (hb : d310056 p = 1) : d245366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d310056 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d310056 q = 1) : d30664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d30664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93475 q ha hb
    | true =>
      simp only [d204, d30664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d310056 q = 1) : d245355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d310056 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d310056 q = 1) : d245356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d310056 q = 1) : d245364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d245364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d245364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d310056 q = 1) : d245365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d245365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d245365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d310056 q = 1) : d245366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d245366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d245366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93477 (p : Pattern) (ha : d231 p = 1) (hb : d310056 p = 1) : d30687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d310056 q = 1) : d30682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d30682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d30682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93472 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d310056 q = 1) : d30639 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d30639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93472 q ha hb
    | true =>
      simp only [d139, d30639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d310056 q = 1) : d30683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d30683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d30683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d310056 q = 1) : d30640 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d30640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d30640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d310056 q = 1) : d30684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d30684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d30684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d310056 q = 1) : d30685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d30685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d30685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d310056 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d310056 q = 1) : d30686 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d30686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d30686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d310056 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d310056 q = 1) : d30687 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d30687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d30687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93478 (p : Pattern) (ha : d237 p = 1) (hb : d310056 p = 1) : d30693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d310056 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d310056 q = 1) : d30688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d30688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93477 q ha hb
    | true =>
      simp only [d232, d30688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d310056 q = 1) : d30689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d30689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d30689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d310056 q = 1) : d30690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d30690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d30690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d310056 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d310056 q = 1) : d30691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d30691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d30691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d310056 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d310056 q = 1) : d30692 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d30692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d30692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d310056 q = 1) : d30693 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d30693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d30693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro93479 (p : Pattern) (ha : d243 p = 1) (hb : d310056 p = 1) : d30699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d310056 q = 1) : d30694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d30694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93478 q ha hb
    | true =>
      simp only [d238, d30694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d310056 q = 1) : d30695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d30695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d30695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d310056 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d310056 q = 1) : d30696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d30696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d30696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d310056 q = 1) : d30697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d30697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d30697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d310056 q = 1) : d30698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d30698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d30698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d310056 q = 1) : d30699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d30699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d30699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro93480 (p : Pattern) (ha : d4359 p = 1) (hb : d310056 p = 1) : d245376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d310056 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d310056 q = 1) : d30700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d30700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93479 q ha hb
    | true =>
      simp only [d244, d30700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d310056 q = 1) : d245372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d245372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d245372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d310056 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d310056 q = 1) : d245373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d245373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d245373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d310056 q = 1) : d245374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d245374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d245374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d310056 q = 1) : d245375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d245375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d245375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d310056 q = 1) : d245376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d245376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d245376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93481 (p : Pattern) (ha : d156 p = 1) (hb : d310056 p = 1) : d30656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310056 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d310056 q = 1) : d30653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d310056 q = 1) : d30654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d310056 q = 1) : d30655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d30655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d30655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d310056 q = 1) : d30656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d30656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d30656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93482 (p : Pattern) (ha : d51643 p = 1) (hb : d310056 p = 1) : d245354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d310056 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d310056 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d310056 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d310056 q = 1) : d30657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93481 q ha hb
    | true =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d310056 q = 1) : d245350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d310056 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d310056 q = 1) : d245351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d310056 q = 1) : d245352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d310056 q = 1) : d245353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d310056 q = 1) : d245354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d245354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d245354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro93483 (p : Pattern) (ha : d51646 p = 1) (hb : d310056 p = 1) : d245359 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d310056 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d310056 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d310056 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d310056 q = 1) : d30657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93481 q ha hb
    | true =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d310056 q = 1) : d245350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d310056 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d310056 q = 1) : d245351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d310056 q = 1) : d245352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d310056 q = 1) : d245353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d310056 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d310056 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d310056 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d310056 q = 1) : d30664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d30664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93475 q ha hb
    | true =>
      simp only [d204, d30664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d310056 q = 1) : d245355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d310056 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d310056 q = 1) : d245356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d310056 q = 1) : d245357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d245357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d245357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d310056 q = 1) : d245358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d245358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d245358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d310056 q = 1) : d245359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d245359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d245359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro93484 (p : Pattern) (ha : d51652 p = 1) (hb : d310056 p = 1) : d245382 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d310056 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d310056 q = 1) : d245360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d245360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93482 q ha hb
    | true =>
      simp only [d51647, d245360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93483 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d310056 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d310056 q = 1) : d245361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d245361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d245361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d310056 q = 1) : d245362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d245362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d245362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d310056 q = 1) : d245363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d245363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d245363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d310056 q = 1) : d245367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d245367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d245367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93476 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d310056 q = 1) : d245368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d245368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d245368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d310056 q = 1) : d245369 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d245369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d245369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d310056 q = 1) : d245370 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d245370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d245370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d310056 q = 1) : d245371 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d245371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d245371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d310056 q = 1) : d245377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d245377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d245377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93480 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d310056 q = 1) : d245378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d245378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d245378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d310056 q = 1) : d245379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d245379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d245379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d310056 q = 1) : d245380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d245380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d245380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d310056 q = 1) : d245381 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d245381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d245381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d310056 q = 1) : d245382 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d245382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d245382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro93485 (p : Pattern) (ha : d284 p = 1) (hb : d310056 p = 1) : d30721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d310056 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d310056 q = 1) : d30657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93481 q ha hb
    | true =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d310056 q = 1) : d30717 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d30717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d30717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d310056 q = 1) : d30718 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d30718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d30718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d310056 q = 1) : d30719 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d30719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d30719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d310056 q = 1) : d30720 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d30720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d30720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d310056 q = 1) : d30721 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d30721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d30721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93486 (p : Pattern) (ha : d291 p = 1) (hb : d310056 p = 1) : d30728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d310056 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d310056 q = 1) : d30657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93481 q ha hb
    | true =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d310056 q = 1) : d30717 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d30717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d30717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d310056 q = 1) : d30718 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d30718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d30718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d310056 q = 1) : d30719 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d30719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d30719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d310056 q = 1) : d30720 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d30720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d30720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d310056 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d310056 q = 1) : d30664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d30664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93475 q ha hb
    | true =>
      simp only [d204, d30664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d310056 q = 1) : d30724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d30724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d30724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d310056 q = 1) : d30725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d30725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d30725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d310056 q = 1) : d30726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d30726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d30726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d310056 q = 1) : d30727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d30727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d30727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d310056 q = 1) : d30728 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d30728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d30728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro93487 (p : Pattern) (ha : d397 p = 1) (hb : d310056 p = 1) : d30834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d310056 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d310056 q = 1) : d30657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93481 q ha hb
    | true =>
      simp only [d157, d30657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d310056 q = 1) : d30717 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d30717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d30717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d310056 q = 1) : d30718 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d30718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d30718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d310056 q = 1) : d30719 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d30719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d30719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d310056 q = 1) : d30720 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d30720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d30720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d310056 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d310056 q = 1) : d30834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d30834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d30834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93488 (p : Pattern) (ha : d296 p = 1) (hb : d310056 p = 1) : d30733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310056 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d310056 q = 1) : d30653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d310056 q = 1) : d30654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d310056 q = 1) : d30732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d30732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d30732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d310056 q = 1) : d30733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d30733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d30733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93489 (p : Pattern) (ha : d303 p = 1) (hb : d310056 p = 1) : d30740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310056 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d310056 q = 1) : d30653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d310056 q = 1) : d30738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d30738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d30738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d310056 q = 1) : d30739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d30739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d30739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d310056 q = 1) : d30740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d30740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d30740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro93490 (p : Pattern) (ha : d4736 p = 1) (hb : d310056 p = 1) : d30805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d310056 q = 1) : d30802 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d30802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d30802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d310056 q = 1) : d30803 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d30803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d30803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d310056 q = 1) : d30804 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d30804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d30804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d310056 q = 1) : d30805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d30805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d30805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro93491 (p : Pattern) (ha : d318 p = 1) (hb : d310056 p = 1) : d30750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d310056 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d310056, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d310056, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d310056 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d310056 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d310056 q = 1) : d30635 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d310056 q = 1) : d30748 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d30748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d30748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d317 q = 1) (hb : d310056 q = 1) : d30749 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d30749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d30749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d310056 q = 1) : d21 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d136 q = 1) (hb : d310056 q = 1) : d30636 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d30636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136, d30636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137 q = 1) (hb : d310056 q = 1) : d30637 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d30637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137, d30637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d318 q = 1) (hb : d310056 q = 1) : d30750 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d30750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318, d30750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro93492 (p : Pattern) (ha : d9381 p = 1) (hb : d310056 p = 1) : d30758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d310056 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d310056, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d310056, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d310056 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d310056 q = 1) : d30635 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d30635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5448 q = 1) (hb : d310056 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d5449 q = 1) (hb : d310056 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5449, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d310056 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9381 q = 1) (hb : d310056 q = 1) : d30758 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d30758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9381, d30758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro93493 (p : Pattern) (ha : d15966 p = 1) (hb : d310056 p = 1) : d30764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d310056 q = 1) : d30751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d30751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93491 q ha hb
    | true =>
      simp only [d319, d30751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d310056 q = 1) : d30752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d30752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d30752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d310056 q = 1) : d30753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d30753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d30753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d310056 q = 1) : d30754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d30754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d30754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d310056 q = 1) : d30639 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d30639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93472 q ha hb
    | true =>
      simp only [d139, d30639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d310056 q = 1) : d30640 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d30640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d30640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d310056 q = 1) : d30641 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d30641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d30641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d310056 q = 1) : d30642 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d30642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d30642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d310056 q = 1) : d30755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d30755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d30755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d310056 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93492 q ha hb
    | true =>
      simp only [d9382, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d310056 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d310056 q = 1) : d30761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d310056 q = 1) : d30762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d310056 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d310056 q = 1) : d30763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d310056 q = 1) : d30764 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d30764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d30764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro93494 (p : Pattern) (ha : d15972 p = 1) (hb : d310056 p = 1) : d30770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d310056 q = 1) : d30765 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d30765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93493 q ha hb
    | true =>
      simp only [d15967, d30765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93473 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d310056 q = 1) : d30766 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d30766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d30766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d310056 q = 1) : d30767 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d30767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d30767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d310056 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d310056 q = 1) : d30645 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d30645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93473 q ha hb
    | true =>
      simp only [d145, d30645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d310056 q = 1) : d30646 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d30646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d30646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d310056 q = 1) : d30647 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d30647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d30647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d310056 q = 1) : d30768 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d30768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d30768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d310056 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d310056 q = 1) : d30648 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d30648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d30648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d310056 q = 1) : d30769 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d30769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d30769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d310056 q = 1) : d30770 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d30770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d30770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro93495 (p : Pattern) (ha : d15978 p = 1) (hb : d310056 p = 1) : d30776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d310056 q = 1) : d30771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d30771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93494 q ha hb
    | true =>
      simp only [d15973, d30771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d310056 q = 1) : d30772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d30772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d30772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d310056 q = 1) : d30773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d30773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d30773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d310056 q = 1) : d30774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d30774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d30774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d310056 q = 1) : d30775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d30775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d30775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d310056 q = 1) : d30776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d30776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d30776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro93496 (p : Pattern) (ha : d128195 p = 1) (hb : d310056 p = 1) : d245392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d310056 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d310056 q = 1) : d30734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d30734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93488 q ha hb
    | true =>
      simp only [d297, d30734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d310056 q = 1) : d30735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d30735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d30735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d310056 q = 1) : d30736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d30736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d30736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d310056 q = 1) : d30737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d30737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d30737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d310056 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d310056 q = 1) : d30741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d30741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93489 q ha hb
    | true =>
      simp only [d304, d30741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d310056 q = 1) : d30742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d30742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d30742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d310056 q = 1) : d30743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d30743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d30743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d310056 q = 1) : d30777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d30777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93495 q ha hb
    | true =>
      simp only [d15979, d30777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93481 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d310056 q = 1) : d245388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d310056 q = 1) : d30806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d30806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93490 q ha hb
    | true =>
      simp only [d4737, d30806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d310056 q = 1) : d30807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d30807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d30807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d310056 q = 1) : d245389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d310056 q = 1) : d245390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d310056 q = 1) : d245391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d310056 q = 1) : d245392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d245392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d245392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro93497 (p : Pattern) (ha : d376 p = 1) (hb : d310056 p = 1) : d30812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310056 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d310056 q = 1) : d30653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d310056 q = 1) : d30654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d30654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d310056 q = 1) : d30732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d30732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d30732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d310056 q = 1) : d30812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d30812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d30812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro93498 (p : Pattern) (ha : d381 p = 1) (hb : d310056 p = 1) : d30817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310056 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d310056 q = 1) : d30653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d30653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d310056 q = 1) : d30738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d30738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d30738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d310056 q = 1) : d30739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d30739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d30739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d310056 q = 1) : d30817 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d30817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d30817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro93499 (p : Pattern) (ha : d5355 p = 1) (hb : d310056 p = 1) : d30826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d310056 q = 1) : d30651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93474 q ha hb
    | true =>
      simp only [d151, d30651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d310056 q = 1) : d30652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d30652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d310056 q = 1) : d30802 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d30802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d30802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d310056 q = 1) : d30803 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d30803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d30803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d310056 q = 1) : d30804 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d30804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d30804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d310056 q = 1) : d30826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d30826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d30826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
