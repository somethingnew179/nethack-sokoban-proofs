import NetHack.Soko22Hazard87.AndIntroBlocks0137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro34500 (p : Pattern) (ha : d14168 p = 1) (hb : d122305 p = 1) : d158685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14163 q = 1) (hb : d122305 q = 1) : d158680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14163, d158680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34499 q ha hb
    | true =>
      simp only [d14163, d158680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14164 q = 1) (hb : d122305 q = 1) : d158681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14164, d158681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14164, d158681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14027 q = 1) (hb : d122305 q = 1) : d158573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34478 q ha hb
    | true =>
      simp only [d14027, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14028 q = 1) (hb : d122305 q = 1) : d158574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14165 q = 1) (hb : d122305 q = 1) : d158682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14165, d158682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14165, d158682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14166 q = 1) (hb : d122305 q = 1) : d158683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14166, d158683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14166, d158683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14167 q = 1) (hb : d122305 q = 1) : d158684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14167, d158684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14167, d158684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14168 q = 1) (hb : d122305 q = 1) : d158685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14168, d158685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14168, d158685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34501 (p : Pattern) (ha : d14189 p = 1) (hb : d122305 p = 1) : d158691 p = 1 := by
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
  have h3 (q : Pattern) (ha : d14186 q = 1) (hb : d122305 q = 1) : d158688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14186, d158688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14186, d158688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14187 q = 1) (hb : d122305 q = 1) : d158689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14187, d158689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14187, d158689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14188 q = 1) (hb : d122305 q = 1) : d158690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14188, d158690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14188, d158690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14189 q = 1) (hb : d122305 q = 1) : d158691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14189, d158691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14189, d158691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34502 (p : Pattern) (ha : d122305 p = 1) (hb : d125477 p = 1) : d158697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14169 q = 1) (hb : d122305 q = 1) : d158686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14169, d158686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34500 q ha hb
    | true =>
      simp only [d14169, d158686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34479 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125473 q = 1) : d158687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, d158687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125473, d158687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14190 q = 1) (hb : d122305 q = 1) : d158692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14190, d158692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34501 q ha hb
    | true =>
      simp only [d14190, d158692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14191 q = 1) (hb : d122305 q = 1) : d158693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14191, d158693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14191, d158693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125474 q = 1) : d158694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, d158694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125474, d158694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125475 q = 1) : d158695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, d158695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125475, d158695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125476 q = 1) : d158696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, d158696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125476, d158696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125477 q = 1) : d158697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, d158697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125477, d158697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34503 (p : Pattern) (ha : d122305 p = 1) (hb : d125483 p = 1) : d158703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14055 q = 1) (hb : d122305 q = 1) : d158601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14055, d158601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14055, d158601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34482 q ha hb
  have h2 (q : Pattern) (ha : d14056 q = 1) (hb : d122305 q = 1) : d158602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14056, d158602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14056, d158602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14062 q = 1) (hb : d122305 q = 1) : d158608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34482 q ha hb
    | true =>
      simp only [d14062, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34483 q ha hb
  have h4 (q : Pattern) (ha : d14063 q = 1) (hb : d122305 q = 1) : d158609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14063, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14064 q = 1) (hb : d122305 q = 1) : d158610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14064, d158610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14064, d158610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125461 q = 1) : d158663 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125461, d158663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34491 q ha hb
    | true =>
      simp only [d125461, d158663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34496 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d122305 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14142 q = 1) (hb : d122305 q = 1) : d158665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14142, d158665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34484 q ha hb
    | true =>
      simp only [d14142, d158665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125462 q = 1) : d158666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125462, d158666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125462, d158666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125463 q = 1) : d158667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, d158667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125463, d158667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125464 q = 1) : d158668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, d158668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125464, d158668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125468 q = 1) : d158672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, d158672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125468, d158672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34497 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d122305 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125469 q = 1) : d158673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, d158673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125469, d158673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125470 q = 1) : d158674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, d158674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125470, d158674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125471 q = 1) : d158675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, d158675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125471, d158675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125472 q = 1) : d158676 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, d158676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125472, d158676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122305 q = 1) (hb : d125478 q = 1) : d158698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, d158698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125478, d158698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34502 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d122305 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d122305 q = 1) (hb : d125479 q = 1) : d158699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, d158699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125479, d158699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d122305 q = 1) (hb : d125480 q = 1) : d158700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, d158700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125480, d158700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122305 q = 1) (hb : d125481 q = 1) : d158701 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, d158701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125481, d158701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125482 q = 1) : d158702 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, d158702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125482, d158702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d122305 q = 1) (hb : d125483 q = 1) : d158703 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, d158703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125483, d158703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro34504 (p : Pattern) (ha : d122305 p = 1) (hb : d125489 p = 1) : d158709 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d122305 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125446 q = 1) : d158591 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125446, d158591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125446, d158591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34481 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125447 q = 1) : d158592 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125447, d158592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125447, d158592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d125448 q = 1) : d158593 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125448, d158593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125448, d158593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125449 q = 1) : d158594 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125449, d158594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125449, d158594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125450 q = 1) : d158595 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125450, d158595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125450, d158595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125484 q = 1) : d158704 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, d158704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125484, d158704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34503 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125485 q = 1) : d158705 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, d158705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125485, d158705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125486 q = 1) : d158706 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, d158706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125486, d158706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125487 q = 1) : d158707 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, d158707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125487, d158707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125488 q = 1) : d158708 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, d158708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125488, d158708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125489 q = 1) : d158709 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, d158709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125489, d158709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro34505 (p : Pattern) (ha : d14210 p = 1) (hb : d122305 p = 1) : d158711 p = 1 := by
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
  have h9 (q : Pattern) (ha : d14208 q = 1) (hb : d122305 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14208, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14209 q = 1) (hb : d122305 q = 1) : d158710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14209, d158710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14209, d158710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14210 q = 1) (hb : d122305 q = 1) : d158711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14210, d158711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14210, d158711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro34506 (p : Pattern) (ha : d14214 p = 1) (hb : d122305 p = 1) : d124070 p = 1 := by
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
  have h5 (q : Pattern) (ha : d14208 q = 1) (hb : d122305 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14208, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14213 q = 1) (hb : d122305 q = 1) : d124069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14213, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14213, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14214 q = 1) (hb : d122305 q = 1) : d124070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14214, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14214, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34507 (p : Pattern) (ha : d14220 p = 1) (hb : d122305 p = 1) : d158717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d122305 q = 1) : d158716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14220 q = 1) (hb : d122305 q = 1) : d158717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14220, d158717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14220, d158717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34508 (p : Pattern) (ha : d14224 p = 1) (hb : d122305 p = 1) : d124080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d122305 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14224 q = 1) (hb : d122305 q = 1) : d124080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14224, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14224, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34509 (p : Pattern) (ha : d14230 p = 1) (hb : d122305 p = 1) : d158723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d122305 q = 1) : d158718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34507 q ha hb
    | true =>
      simp only [d14225, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34508 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d122305 q = 1) : d158719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d122305 q = 1) : d158720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d122305 q = 1) : d158721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d122305 q = 1) : d158722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14230 q = 1) (hb : d122305 q = 1) : d158723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34510 (p : Pattern) (ha : d14233 p = 1) (hb : d122305 p = 1) : d158726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d122305 q = 1) : d158716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14233 q = 1) (hb : d122305 q = 1) : d158726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14233, d158726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14233, d158726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34511 (p : Pattern) (ha : d14234 p = 1) (hb : d122305 p = 1) : d124090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d122305 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14234 q = 1) (hb : d122305 q = 1) : d124090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14234, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14234, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34512 (p : Pattern) (ha : d14240 p = 1) (hb : d122305 p = 1) : d158732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d122305 q = 1) : d158718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34507 q ha hb
    | true =>
      simp only [d14225, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34508 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d122305 q = 1) : d158719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d122305 q = 1) : d158720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d122305 q = 1) : d158721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d122305 q = 1) : d158722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14235 q = 1) (hb : d122305 q = 1) : d158727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34510 q ha hb
    | true =>
      simp only [d14235, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34511 q ha hb
  have h7 (q : Pattern) (ha : d14236 q = 1) (hb : d122305 q = 1) : d158728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14237 q = 1) (hb : d122305 q = 1) : d158729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14237, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14238 q = 1) (hb : d122305 q = 1) : d158730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14239 q = 1) (hb : d122305 q = 1) : d158731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14240 q = 1) (hb : d122305 q = 1) : d158732 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14240, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34513 (p : Pattern) (ha : d14349 p = 1) (hb : d122305 p = 1) : d158793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d122305 q = 1) : d158718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34507 q ha hb
    | true =>
      simp only [d14225, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34508 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d122305 q = 1) : d158719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d122305 q = 1) : d158720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d122305 q = 1) : d158721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d122305 q = 1) : d158722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14344 q = 1) (hb : d122305 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34508 q ha hb
    | true =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14345 q = 1) (hb : d122305 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14346 q = 1) (hb : d122305 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14347 q = 1) (hb : d122305 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14348 q = 1) (hb : d122305 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14349 q = 1) (hb : d122305 q = 1) : d158793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14349, d158793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14349, d158793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34514 (p : Pattern) (ha : d14355 p = 1) (hb : d122305 p = 1) : d124175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14344 q = 1) (hb : d122305 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34508 q ha hb
    | true =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14345 q = 1) (hb : d122305 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14346 q = 1) (hb : d122305 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14347 q = 1) (hb : d122305 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14348 q = 1) (hb : d122305 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14350 q = 1) (hb : d122305 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34511 q ha hb
    | true =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14351 q = 1) (hb : d122305 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14352 q = 1) (hb : d122305 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14353 q = 1) (hb : d122305 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14354 q = 1) (hb : d122305 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14355 q = 1) (hb : d122305 q = 1) : d124175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14355, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14355, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34515 (p : Pattern) (ha : d14364 p = 1) (hb : d122305 p = 1) : d124184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14350 q = 1) (hb : d122305 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34511 q ha hb
    | true =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14351 q = 1) (hb : d122305 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14352 q = 1) (hb : d122305 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14353 q = 1) (hb : d122305 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14354 q = 1) (hb : d122305 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14364 q = 1) (hb : d122305 q = 1) : d124184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14364, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14364, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34516 (p : Pattern) (ha : d14395 p = 1) (hb : d122305 p = 1) : d124204 p = 1 := by
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
  have h5 (q : Pattern) (ha : d14385 q = 1) (hb : d122305 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14385, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14394 q = 1) (hb : d122305 q = 1) : d124203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14394, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14394, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14395 q = 1) (hb : d122305 q = 1) : d124204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14395, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14395, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34517 (p : Pattern) (ha : d14447 p = 1) (hb : d122305 p = 1) : d124227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14396 q = 1) (hb : d122305 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34516 q ha hb
    | true =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14397 q = 1) (hb : d122305 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14444 q = 1) (hb : d122305 q = 1) : d124224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14444, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14444, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14445 q = 1) (hb : d122305 q = 1) : d124225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14445, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14445, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14446 q = 1) (hb : d122305 q = 1) : d124226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14446, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14446, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14447 q = 1) (hb : d122305 q = 1) : d124227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14447, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14447, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34518 (p : Pattern) (ha : d14453 p = 1) (hb : d122305 p = 1) : d124233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14448 q = 1) (hb : d122305 q = 1) : d124228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14448, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34517 q ha hb
    | true =>
      simp only [d14448, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14449 q = 1) (hb : d122305 q = 1) : d124229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14449, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14449, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14450 q = 1) (hb : d122305 q = 1) : d124230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14450, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14450, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14451 q = 1) (hb : d122305 q = 1) : d124231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14451, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14451, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14452 q = 1) (hb : d122305 q = 1) : d124232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14452, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14452, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14453 q = 1) (hb : d122305 q = 1) : d124233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14453, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14453, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34519 (p : Pattern) (ha : d14245 p = 1) (hb : d122305 p = 1) : d158737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d122305 q = 1) : d158736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14245 q = 1) (hb : d122305 q = 1) : d158737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14245, d158737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14245, d158737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34520 (p : Pattern) (ha : d14247 p = 1) (hb : d122305 p = 1) : d124103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d122305 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14247 q = 1) (hb : d122305 q = 1) : d124103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14247, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14247, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34521 (p : Pattern) (ha : d14254 p = 1) (hb : d122305 p = 1) : d158744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d122305 q = 1) : d158742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d122305 q = 1) : d158743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14254 q = 1) (hb : d122305 q = 1) : d158744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14254, d158744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14254, d158744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34522 (p : Pattern) (ha : d14257 p = 1) (hb : d122305 p = 1) : d124113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d122305 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d122305 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14257 q = 1) (hb : d122305 q = 1) : d124113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14257, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14257, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34523 (p : Pattern) (ha : d14263 p = 1) (hb : d122305 p = 1) : d124117 p = 1 := by
  have h0 (q : Pattern) (ha : d14261 q = 1) (hb : d122304 q = 1) : d14261 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14262 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14263 q = 1) (hb : d122305 q = 1) : d124117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14263, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14263, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34524 (p : Pattern) (ha : d14267 p = 1) (hb : d122305 p = 1) : d158748 p = 1 := by
  have h0 (q : Pattern) (ha : d14078 q = 1) (hb : d122304 q = 1) : d14078 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14267 q = 1) (hb : d122305 q = 1) : d158748 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14267, d122305, d158748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14267, d122305, d158748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34525 (p : Pattern) (ha : d14273 p = 1) (hb : d122305 p = 1) : d158754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14264 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14264, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14264, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
  have h2 (q : Pattern) (ha : d14265 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14265, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14265, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14266 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14266, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14266, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14268 q = 1) (hb : d122305 q = 1) : d158749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14268, d158749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
    | true =>
      simp only [d14268, d158749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34524 q ha hb
  have h5 (q : Pattern) (ha : d14269 q = 1) (hb : d122305 q = 1) : d158750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14269, d158750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14269, d158750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14270 q = 1) (hb : d122305 q = 1) : d158751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14270, d158751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14270, d158751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14271 q = 1) (hb : d122305 q = 1) : d158752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14271, d158752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14271, d158752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14080 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
    | true =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
  have h9 (q : Pattern) (ha : d14081 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14082 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14083 q = 1) (hb : d122305 q = 1) : d158623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14083, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14272 q = 1) (hb : d122305 q = 1) : d158753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14272, d158753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14272, d158753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14273 q = 1) (hb : d122305 q = 1) : d158754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14273, d158754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14273, d158754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro34526 (p : Pattern) (ha : d14279 p = 1) (hb : d122305 p = 1) : d158760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d122305 q = 1) : d158755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34525 q ha hb
    | true =>
      simp only [d14274, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d122305 q = 1) : d158756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d122305 q = 1) : d158757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d122305 q = 1) : d158758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d122305 q = 1) : d158759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14279 q = 1) (hb : d122305 q = 1) : d158760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14279, d158760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14279, d158760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34527 (p : Pattern) (ha : d14312 p = 1) (hb : d122305 p = 1) : d158766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d122305 q = 1) : d158763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d122305 q = 1) : d158764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d122305 q = 1) : d158765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14312 q = 1) (hb : d122305 q = 1) : d158766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14312, d158766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14312, d158766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34528 (p : Pattern) (ha : d122305 p = 1) (hb : d125494 p = 1) : d158772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d122305 q = 1) : d158738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34519 q ha hb
    | true =>
      simp only [d14248, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34520 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d122305 q = 1) : d158739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d122305 q = 1) : d158740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d122305 q = 1) : d158741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d122305 q = 1) : d158745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34521 q ha hb
    | true =>
      simp only [d14258, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34522 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d122305 q = 1) : d158746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d122305 q = 1) : d158747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d122305 q = 1) : d158761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34526 q ha hb
    | true =>
      simp only [d14280, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34507 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125490 q = 1) : d158762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125490, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d122305 q = 1) : d158767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34527 q ha hb
    | true =>
      simp only [d14313, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d122305 q = 1) : d158768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125491 q = 1) : d158769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125492 q = 1) : d158770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125492, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125493 q = 1) : d158771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125493, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125494 q = 1) : d158772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125494, d158772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125494, d158772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34529 (p : Pattern) (ha : d14319 p = 1) (hb : d122305 p = 1) : d158773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d122305 q = 1) : d158736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14319 q = 1) (hb : d122305 q = 1) : d158773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14319, d158773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14319, d158773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34530 (p : Pattern) (ha : d14320 p = 1) (hb : d122305 p = 1) : d124143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d122305 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14320 q = 1) (hb : d122305 q = 1) : d124143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14320, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14320, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34531 (p : Pattern) (ha : d14325 p = 1) (hb : d122305 p = 1) : d158778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d122305 q = 1) : d158742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d122305 q = 1) : d158743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14325 q = 1) (hb : d122305 q = 1) : d158778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14325, d158778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14325, d158778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34532 (p : Pattern) (ha : d14326 p = 1) (hb : d122305 p = 1) : d124149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34506 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d122305 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d122305 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14326 q = 1) (hb : d122305 q = 1) : d124149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14326, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14326, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34533 (p : Pattern) (ha : d14330 p = 1) (hb : d122305 p = 1) : d158782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d122305 q = 1) : d158755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34525 q ha hb
    | true =>
      simp only [d14274, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d122305 q = 1) : d158756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d122305 q = 1) : d158757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d122305 q = 1) : d158758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d122305 q = 1) : d158759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14330 q = 1) (hb : d122305 q = 1) : d158782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14330, d158782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14330, d158782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34534 (p : Pattern) (ha : d14336 p = 1) (hb : d122305 p = 1) : d158785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34505 q ha hb
    | true =>
      simp only [d14211, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d122305 q = 1) : d158763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d122305 q = 1) : d158764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d122305 q = 1) : d158765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14336 q = 1) (hb : d122305 q = 1) : d158785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14336, d158785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14336, d158785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34535 (p : Pattern) (ha : d122305 p = 1) (hb : d125499 p = 1) : d158791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d122305 q = 1) : d158738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34519 q ha hb
    | true =>
      simp only [d14248, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34520 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d122305 q = 1) : d158739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d122305 q = 1) : d158740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d122305 q = 1) : d158741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d122305 q = 1) : d158745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34521 q ha hb
    | true =>
      simp only [d14258, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34522 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d122305 q = 1) : d158746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d122305 q = 1) : d158747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d122305 q = 1) : d158761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34526 q ha hb
    | true =>
      simp only [d14280, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34507 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125490 q = 1) : d158762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125490, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d122305 q = 1) : d158767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34527 q ha hb
    | true =>
      simp only [d14313, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d122305 q = 1) : d158768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125491 q = 1) : d158769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125492 q = 1) : d158770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125492, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125493 q = 1) : d158771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125493, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14321 q = 1) (hb : d122305 q = 1) : d158774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14321, d158774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34529 q ha hb
    | true =>
      simp only [d14321, d158774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34530 q ha hb
  have h16 (q : Pattern) (ha : d14322 q = 1) (hb : d122305 q = 1) : d158775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14322, d158775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14322, d158775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14323 q = 1) (hb : d122305 q = 1) : d158776 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14323, d158776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14323, d158776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14324 q = 1) (hb : d122305 q = 1) : d158777 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14324, d158777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14324, d158777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14327 q = 1) (hb : d122305 q = 1) : d158779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14327, d158779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34531 q ha hb
    | true =>
      simp only [d14327, d158779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34532 q ha hb
  have h20 (q : Pattern) (ha : d14328 q = 1) (hb : d122305 q = 1) : d158780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14328, d158780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14328, d158780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14329 q = 1) (hb : d122305 q = 1) : d158781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14329, d158781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14329, d158781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14331 q = 1) (hb : d122305 q = 1) : d158783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34533 q ha hb
    | true =>
      simp only [d14331, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34510 q ha hb
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125495 q = 1) : d158784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125495, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14337 q = 1) (hb : d122305 q = 1) : d158786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34534 q ha hb
    | true =>
      simp only [d14337, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14338 q = 1) (hb : d122305 q = 1) : d158787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14338, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122305 q = 1) (hb : d125496 q = 1) : d158788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125496, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122305 q = 1) (hb : d125497 q = 1) : d158789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125497, d158789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125497, d158789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122305 q = 1) (hb : d125498 q = 1) : d158790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125498, d158790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125498, d158790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122305 q = 1) (hb : d125499 q = 1) : d158791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125499, d158791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125499, d158791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34536 (p : Pattern) (ha : d122305 p = 1) (hb : d125506 p = 1) : d158800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14331 q = 1) (hb : d122305 q = 1) : d158783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34533 q ha hb
    | true =>
      simp only [d14331, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34510 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125495 q = 1) : d158784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125495, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14337 q = 1) (hb : d122305 q = 1) : d158786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34534 q ha hb
    | true =>
      simp only [d14337, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14338 q = 1) (hb : d122305 q = 1) : d158787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14338, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125496 q = 1) : d158788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125496, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125504 q = 1) : d158798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125504, d158798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125504, d158798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125505 q = 1) : d158799 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125505, d158799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125505, d158799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125506 q = 1) : d158800 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, d158800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125506, d158800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34537 (p : Pattern) (ha : d14372 p = 1) (hb : d122305 p = 1) : d124190 p = 1 := by
  have h0 (q : Pattern) (ha : d14370 q = 1) (hb : d122304 q = 1) : d14370 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14371 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14372 q = 1) (hb : d122305 q = 1) : d124190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14372, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14372, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34538 (p : Pattern) (ha : d14376 p = 1) (hb : d122305 p = 1) : d158806 p = 1 := by
  have h0 (q : Pattern) (ha : d14155 q = 1) (hb : d122304 q = 1) : d14155 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14376 q = 1) (hb : d122305 q = 1) : d158806 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14376, d122305, d158806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14376, d122305, d158806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34539 (p : Pattern) (ha : d14382 p = 1) (hb : d122305 p = 1) : d158812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14373 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14373, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14373, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
  have h2 (q : Pattern) (ha : d14374 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14374, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14374, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14375 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14375, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14375, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14377 q = 1) (hb : d122305 q = 1) : d158807 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14377, d158807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
    | true =>
      simp only [d14377, d158807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34538 q ha hb
  have h5 (q : Pattern) (ha : d14378 q = 1) (hb : d122305 q = 1) : d158808 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14378, d158808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14378, d158808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14379 q = 1) (hb : d122305 q = 1) : d158809 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14379, d158809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14379, d158809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14380 q = 1) (hb : d122305 q = 1) : d158810 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14380, d158810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14380, d158810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14157 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
    | true =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
  have h9 (q : Pattern) (ha : d14158 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14159 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14160 q = 1) (hb : d122305 q = 1) : d158677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14160, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14381 q = 1) (hb : d122305 q = 1) : d158811 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14381, d158811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14381, d158811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14382 q = 1) (hb : d122305 q = 1) : d158812 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14382, d158812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14382, d158812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro34540 (p : Pattern) (ha : d14387 p = 1) (hb : d122305 p = 1) : d158816 p = 1 := by
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
  have h9 (q : Pattern) (ha : d14385 q = 1) (hb : d122305 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14385, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14386 q = 1) (hb : d122305 q = 1) : d158815 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14386, d158815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14386, d158815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14387 q = 1) (hb : d122305 q = 1) : d158816 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14387, d158816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14387, d158816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro34541 (p : Pattern) (ha : d14393 p = 1) (hb : d122305 p = 1) : d158822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14383 q = 1) (hb : d122305 q = 1) : d158813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14383, d158813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34539 q ha hb
    | true =>
      simp only [d14383, d158813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14384 q = 1) (hb : d122305 q = 1) : d158814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14384, d158814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14384, d158814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14388 q = 1) (hb : d122305 q = 1) : d158817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34540 q ha hb
    | true =>
      simp only [d14388, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14389 q = 1) (hb : d122305 q = 1) : d158818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14390 q = 1) (hb : d122305 q = 1) : d158819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14390, d158819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14390, d158819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14391 q = 1) (hb : d122305 q = 1) : d158820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14391, d158820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14391, d158820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14392 q = 1) (hb : d122305 q = 1) : d158821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14392, d158821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14392, d158821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14393 q = 1) (hb : d122305 q = 1) : d158822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14393, d158822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14393, d158822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34542 (p : Pattern) (ha : d14401 p = 1) (hb : d122305 p = 1) : d158826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d122305 q = 1) : d158817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34540 q ha hb
    | true =>
      simp only [d14388, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d122305 q = 1) : d158818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14396 q = 1) (hb : d122305 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34516 q ha hb
    | true =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14397 q = 1) (hb : d122305 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14398 q = 1) (hb : d122305 q = 1) : d158823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14398, d158823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14398, d158823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14399 q = 1) (hb : d122305 q = 1) : d158824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14399, d158824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14399, d158824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14400 q = 1) (hb : d122305 q = 1) : d158825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14400, d158825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14400, d158825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14401 q = 1) (hb : d122305 q = 1) : d158826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14401, d158826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14401, d158826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34543 (p : Pattern) (ha : d14436 p = 1) (hb : d122305 p = 1) : d158832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d122305 q = 1) : d158817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34540 q ha hb
    | true =>
      simp only [d14388, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d122305 q = 1) : d158818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14433 q = 1) (hb : d122305 q = 1) : d158829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14433, d158829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14433, d158829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14434 q = 1) (hb : d122305 q = 1) : d158830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14434, d158830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14434, d158830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14435 q = 1) (hb : d122305 q = 1) : d158831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14435, d158831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14435, d158831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14436 q = 1) (hb : d122305 q = 1) : d158832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14436, d158832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14436, d158832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34544 (p : Pattern) (ha : d122305 p = 1) (hb : d125516 p = 1) : d158838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14402 q = 1) (hb : d122305 q = 1) : d158827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14402, d158827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34541 q ha hb
    | true =>
      simp only [d14402, d158827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34542 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125512 q = 1) : d158828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, d158828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125512, d158828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14437 q = 1) (hb : d122305 q = 1) : d158833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14437, d158833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34543 q ha hb
    | true =>
      simp only [d14437, d158833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14438 q = 1) (hb : d122305 q = 1) : d158834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14438, d158834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14438, d158834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125513 q = 1) : d158835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, d158835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125513, d158835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125514 q = 1) : d158836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, d158836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125514, d158836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125515 q = 1) : d158837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, d158837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125515, d158837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125516 q = 1) : d158838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, d158838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125516, d158838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34545 (p : Pattern) (ha : d122305 p = 1) (hb : d125522 p = 1) : d158844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14231 q = 1) (hb : d122305 q = 1) : d158724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14231, d158724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14231, d158724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34509 q ha hb
  have h2 (q : Pattern) (ha : d14232 q = 1) (hb : d122305 q = 1) : d158725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14232, d158725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14232, d158725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14241 q = 1) (hb : d122305 q = 1) : d158733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34509 q ha hb
    | true =>
      simp only [d14241, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34512 q ha hb
  have h4 (q : Pattern) (ha : d14242 q = 1) (hb : d122305 q = 1) : d158734 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14242, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14243 q = 1) (hb : d122305 q = 1) : d158735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14243, d158735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14243, d158735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125500 q = 1) : d158792 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125500, d158792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34528 q ha hb
    | true =>
      simp only [d125500, d158792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34535 q ha hb
  have h7 (q : Pattern) (ha : d14356 q = 1) (hb : d122305 q = 1) : d158794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14356, d158794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34513 q ha hb
    | true =>
      simp only [d14356, d158794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34514 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125501 q = 1) : d158795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125501, d158795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125501, d158795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125502 q = 1) : d158796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, d158796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125502, d158796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125503 q = 1) : d158797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, d158797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125503, d158797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125507 q = 1) : d158801 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, d158801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125507, d158801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34536 q ha hb
  have h12 (q : Pattern) (ha : d14365 q = 1) (hb : d122305 q = 1) : d124185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14365, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14365, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34515 q ha hb
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125508 q = 1) : d158802 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, d158802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125508, d158802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125509 q = 1) : d158803 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, d158803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125509, d158803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125510 q = 1) : d158804 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, d158804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125510, d158804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125511 q = 1) : d158805 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, d158805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125511, d158805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125517 q = 1) : d158839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, d158839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125517, d158839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34544 q ha hb
  have h18 (q : Pattern) (ha : d14454 q = 1) (hb : d122305 q = 1) : d124234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14454, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14454, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34518 q ha hb
  have h19 (q : Pattern) (ha : d122305 q = 1) (hb : d125518 q = 1) : d158840 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, d158840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125518, d158840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122305 q = 1) (hb : d125519 q = 1) : d158841 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, d158841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125519, d158841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122305 q = 1) (hb : d125520 q = 1) : d158842 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, d158842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125520, d158842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122305 q = 1) (hb : d125521 q = 1) : d158843 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, d158843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125521, d158843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125522 q = 1) : d158844 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, d158844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125522, d158844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34546 (p : Pattern) (ha : d122305 p = 1) (hb : d125528 p = 1) : d158850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d125523 q = 1) : d158845 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, d158845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125523, d158845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34545 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125524 q = 1) : d158846 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, d158846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125524, d158846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125525 q = 1) : d158847 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, d158847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125525, d158847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d125526 q = 1) : d158848 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, d158848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125526, d158848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125527 q = 1) : d158849 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, d158849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125527, d158849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125528 q = 1) : d158850 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, d158850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125528, d158850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34547 (p : Pattern) (ha : d14467 p = 1) (hb : d122305 p = 1) : d123974 p = 1 := by
  have h0 (q : Pattern) (ha : d14077 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14467 q = 1) (hb : d122305 q = 1) : d123974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14467, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14467, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34548 (p : Pattern) (ha : d14477 p = 1) (hb : d122305 p = 1) : d158854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14468 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
  have h2 (q : Pattern) (ha : d14469 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14470 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14471 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
    | true =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14472 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14473 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14474 q = 1) (hb : d122305 q = 1) : d158852 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14474, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14475 q = 1) (hb : d122305 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14475, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14476 q = 1) (hb : d122305 q = 1) : d158853 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14476, d158853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14476, d158853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14477 q = 1) (hb : d122305 q = 1) : d158854 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14477, d158854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14477, d158854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro34549 (p : Pattern) (ha : d14481 p = 1) (hb : d122305 p = 1) : d124256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14471 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
    | true =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14472 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14473 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14475 q = 1) (hb : d122305 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14475, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14480 q = 1) (hb : d122305 q = 1) : d124255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14480, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14480, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14481 q = 1) (hb : d122305 q = 1) : d124256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14481, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14481, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34550 (p : Pattern) (ha : d14487 p = 1) (hb : d122305 p = 1) : d158860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d122305 q = 1) : d158859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14487 q = 1) (hb : d122305 q = 1) : d158860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14487, d158860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14487, d158860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34551 (p : Pattern) (ha : d14491 p = 1) (hb : d122305 p = 1) : d124266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d122305 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14491 q = 1) (hb : d122305 q = 1) : d124266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14491, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14491, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34552 (p : Pattern) (ha : d14497 p = 1) (hb : d122305 p = 1) : d158866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d122305 q = 1) : d158861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34550 q ha hb
    | true =>
      simp only [d14492, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34551 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d122305 q = 1) : d158862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d122305 q = 1) : d158863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d122305 q = 1) : d158864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d122305 q = 1) : d158865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14497 q = 1) (hb : d122305 q = 1) : d158866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34553 (p : Pattern) (ha : d14500 p = 1) (hb : d122305 p = 1) : d158869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d122305 q = 1) : d158859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14500 q = 1) (hb : d122305 q = 1) : d158869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14500, d158869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14500, d158869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34554 (p : Pattern) (ha : d14501 p = 1) (hb : d122305 p = 1) : d124276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d122305 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14501 q = 1) (hb : d122305 q = 1) : d124276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14501, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14501, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34555 (p : Pattern) (ha : d14507 p = 1) (hb : d122305 p = 1) : d158875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d122305 q = 1) : d158861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34550 q ha hb
    | true =>
      simp only [d14492, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34551 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d122305 q = 1) : d158862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d122305 q = 1) : d158863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d122305 q = 1) : d158864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d122305 q = 1) : d158865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14502 q = 1) (hb : d122305 q = 1) : d158870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34553 q ha hb
    | true =>
      simp only [d14502, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34554 q ha hb
  have h7 (q : Pattern) (ha : d14503 q = 1) (hb : d122305 q = 1) : d158871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14504 q = 1) (hb : d122305 q = 1) : d158872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14504, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14505 q = 1) (hb : d122305 q = 1) : d158873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14506 q = 1) (hb : d122305 q = 1) : d158874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14507 q = 1) (hb : d122305 q = 1) : d158875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14507, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34556 (p : Pattern) (ha : d14622 p = 1) (hb : d122305 p = 1) : d158936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d122305 q = 1) : d158861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34550 q ha hb
    | true =>
      simp only [d14492, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34551 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d122305 q = 1) : d158862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d122305 q = 1) : d158863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d122305 q = 1) : d158864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d122305 q = 1) : d158865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14617 q = 1) (hb : d122305 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34551 q ha hb
    | true =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14618 q = 1) (hb : d122305 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14619 q = 1) (hb : d122305 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14620 q = 1) (hb : d122305 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14621 q = 1) (hb : d122305 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14622 q = 1) (hb : d122305 q = 1) : d158936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14622, d158936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14622, d158936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34557 (p : Pattern) (ha : d14628 p = 1) (hb : d122305 p = 1) : d124361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14617 q = 1) (hb : d122305 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34551 q ha hb
    | true =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14618 q = 1) (hb : d122305 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14619 q = 1) (hb : d122305 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14620 q = 1) (hb : d122305 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14621 q = 1) (hb : d122305 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14623 q = 1) (hb : d122305 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34554 q ha hb
    | true =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14624 q = 1) (hb : d122305 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14625 q = 1) (hb : d122305 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14626 q = 1) (hb : d122305 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14627 q = 1) (hb : d122305 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14628 q = 1) (hb : d122305 q = 1) : d124361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14628, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14628, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34558 (p : Pattern) (ha : d14637 p = 1) (hb : d122305 p = 1) : d124370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14623 q = 1) (hb : d122305 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34554 q ha hb
    | true =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14624 q = 1) (hb : d122305 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14625 q = 1) (hb : d122305 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14626 q = 1) (hb : d122305 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14627 q = 1) (hb : d122305 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14637 q = 1) (hb : d122305 q = 1) : d124370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14637, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14637, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34559 (p : Pattern) (ha : d14658 p = 1) (hb : d122305 p = 1) : d124032 p = 1 := by
  have h0 (q : Pattern) (ha : d14154 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14658 q = 1) (hb : d122305 q = 1) : d124032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14658, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14658, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34560 (p : Pattern) (ha : d14680 p = 1) (hb : d122305 p = 1) : d124398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14662 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
    | true =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14663 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14664 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14670 q = 1) (hb : d122305 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14670, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14679 q = 1) (hb : d122305 q = 1) : d124397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14679, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14679, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14680 q = 1) (hb : d122305 q = 1) : d124398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14680, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14680, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro34561 (p : Pattern) (ha : d14736 p = 1) (hb : d122305 p = 1) : d124421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14681 q = 1) (hb : d122305 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34560 q ha hb
    | true =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14682 q = 1) (hb : d122305 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14733 q = 1) (hb : d122305 q = 1) : d124418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14733, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14733, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14734 q = 1) (hb : d122305 q = 1) : d124419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14734, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14734, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14735 q = 1) (hb : d122305 q = 1) : d124420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14735, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14735, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14736 q = 1) (hb : d122305 q = 1) : d124421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14736, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14736, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34562 (p : Pattern) (ha : d14742 p = 1) (hb : d122305 p = 1) : d124427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14737 q = 1) (hb : d122305 q = 1) : d124422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14737, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34561 q ha hb
    | true =>
      simp only [d14737, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14738 q = 1) (hb : d122305 q = 1) : d124423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14738, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14738, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14739 q = 1) (hb : d122305 q = 1) : d124424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14739, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14739, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14740 q = 1) (hb : d122305 q = 1) : d124425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14740, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14740, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14741 q = 1) (hb : d122305 q = 1) : d124426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14741, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14741, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14742 q = 1) (hb : d122305 q = 1) : d124427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14742, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14742, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34563 (p : Pattern) (ha : d14512 p = 1) (hb : d122305 p = 1) : d158880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d122305 q = 1) : d158879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14512 q = 1) (hb : d122305 q = 1) : d158880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14512, d158880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14512, d158880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34564 (p : Pattern) (ha : d14514 p = 1) (hb : d122305 p = 1) : d124289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d122305 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14514 q = 1) (hb : d122305 q = 1) : d124289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14514, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14514, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34565 (p : Pattern) (ha : d14521 p = 1) (hb : d122305 p = 1) : d158887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d122305 q = 1) : d158885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d122305 q = 1) : d158886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14521 q = 1) (hb : d122305 q = 1) : d158887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14521, d158887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14521, d158887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34566 (p : Pattern) (ha : d14524 p = 1) (hb : d122305 p = 1) : d124299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d122305 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d122305 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14524 q = 1) (hb : d122305 q = 1) : d124299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14524, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14524, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34567 (p : Pattern) (ha : d14532 p = 1) (hb : d122305 p = 1) : d124303 p = 1 := by
  have h0 (q : Pattern) (ha : d14528 q = 1) (hb : d122304 q = 1) : d14528 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14531 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14532 q = 1) (hb : d122305 q = 1) : d124303 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14532, d122305, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14532, d122305, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34568 (p : Pattern) (ha : d14536 p = 1) (hb : d122305 p = 1) : d158891 p = 1 := by
  have h0 (q : Pattern) (ha : d14262 q = 1) (hb : d122304 q = 1) : d14262 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14536 q = 1) (hb : d122305 q = 1) : d158891 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14536, d122305, d158891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14536, d122305, d158891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34569 (p : Pattern) (ha : d14542 p = 1) (hb : d122305 p = 1) : d158897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14533 q = 1) (hb : d122305 q = 1) : d124304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14533, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34567 q ha hb
    | true =>
      simp only [d14533, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
  have h2 (q : Pattern) (ha : d14534 q = 1) (hb : d122305 q = 1) : d124305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14534, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14534, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14535 q = 1) (hb : d122305 q = 1) : d124306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14535, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14535, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14537 q = 1) (hb : d122305 q = 1) : d158892 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14537, d158892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14537, d158892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34568 q ha hb
  have h5 (q : Pattern) (ha : d14538 q = 1) (hb : d122305 q = 1) : d158893 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14538, d158893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14538, d158893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14539 q = 1) (hb : d122305 q = 1) : d158894 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14539, d158894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14539, d158894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14540 q = 1) (hb : d122305 q = 1) : d158895 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14540, d158895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14540, d158895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14468 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
  have h9 (q : Pattern) (ha : d14469 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14470 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14471 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
    | true =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14472 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14473 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14474 q = 1) (hb : d122305 q = 1) : d158852 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14474, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14541 q = 1) (hb : d122305 q = 1) : d158896 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14541, d158896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14541, d158896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14542 q = 1) (hb : d122305 q = 1) : d158897 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14542, d158897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14542, d158897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro34570 (p : Pattern) (ha : d14548 p = 1) (hb : d122305 p = 1) : d158903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d122305 q = 1) : d158898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34569 q ha hb
    | true =>
      simp only [d14543, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d122305 q = 1) : d158899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d122305 q = 1) : d158900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d122305 q = 1) : d158901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d122305 q = 1) : d158902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14548 q = 1) (hb : d122305 q = 1) : d158903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14548, d158903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14548, d158903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34571 (p : Pattern) (ha : d14585 p = 1) (hb : d122305 p = 1) : d158909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d122305 q = 1) : d158906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d122305 q = 1) : d158907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d122305 q = 1) : d158908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14585 q = 1) (hb : d122305 q = 1) : d158909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14585, d158909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14585, d158909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34572 (p : Pattern) (ha : d122305 p = 1) (hb : d125534 p = 1) : d158915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d122305 q = 1) : d158881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34563 q ha hb
    | true =>
      simp only [d14515, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34564 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d122305 q = 1) : d158882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d122305 q = 1) : d158883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d122305 q = 1) : d158884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d122305 q = 1) : d158888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34565 q ha hb
    | true =>
      simp only [d14525, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34566 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d122305 q = 1) : d158889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d122305 q = 1) : d158890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d122305 q = 1) : d158904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34570 q ha hb
    | true =>
      simp only [d14549, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34550 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125530 q = 1) : d158905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125530, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d122305 q = 1) : d158910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34571 q ha hb
    | true =>
      simp only [d14586, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d122305 q = 1) : d158911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125531 q = 1) : d158912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125532 q = 1) : d158913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125532, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125533 q = 1) : d158914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125533, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125534 q = 1) : d158915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, d158915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125534, d158915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34573 (p : Pattern) (ha : d14592 p = 1) (hb : d122305 p = 1) : d158916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d122305 q = 1) : d158879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14592 q = 1) (hb : d122305 q = 1) : d158916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14592, d158916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14592, d158916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34574 (p : Pattern) (ha : d14593 p = 1) (hb : d122305 p = 1) : d124329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d122305 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14593 q = 1) (hb : d122305 q = 1) : d124329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14593, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14593, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34575 (p : Pattern) (ha : d14598 p = 1) (hb : d122305 p = 1) : d158921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d122305 q = 1) : d158885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d122305 q = 1) : d158886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14598 q = 1) (hb : d122305 q = 1) : d158921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14598, d158921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14598, d158921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34576 (p : Pattern) (ha : d14599 p = 1) (hb : d122305 p = 1) : d124335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34549 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d122305 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d122305 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14599 q = 1) (hb : d122305 q = 1) : d124335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14599, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14599, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34577 (p : Pattern) (ha : d14603 p = 1) (hb : d122305 p = 1) : d158925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d122305 q = 1) : d158898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34569 q ha hb
    | true =>
      simp only [d14543, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d122305 q = 1) : d158899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d122305 q = 1) : d158900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d122305 q = 1) : d158901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d122305 q = 1) : d158902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14603 q = 1) (hb : d122305 q = 1) : d158925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14603, d158925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14603, d158925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34578 (p : Pattern) (ha : d14609 p = 1) (hb : d122305 p = 1) : d158928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34548 q ha hb
    | true =>
      simp only [d14478, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d122305 q = 1) : d158906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d122305 q = 1) : d158907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d122305 q = 1) : d158908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14609 q = 1) (hb : d122305 q = 1) : d158928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14609, d158928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14609, d158928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34579 (p : Pattern) (ha : d122305 p = 1) (hb : d125539 p = 1) : d158934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d122305 q = 1) : d158881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34563 q ha hb
    | true =>
      simp only [d14515, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34564 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d122305 q = 1) : d158882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d122305 q = 1) : d158883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d122305 q = 1) : d158884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d122305 q = 1) : d158888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34565 q ha hb
    | true =>
      simp only [d14525, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34566 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d122305 q = 1) : d158889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d122305 q = 1) : d158890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d122305 q = 1) : d158904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34570 q ha hb
    | true =>
      simp only [d14549, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34550 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125530 q = 1) : d158905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125530, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d122305 q = 1) : d158910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34571 q ha hb
    | true =>
      simp only [d14586, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d122305 q = 1) : d158911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125531 q = 1) : d158912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125532 q = 1) : d158913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125532, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125533 q = 1) : d158914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125533, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14594 q = 1) (hb : d122305 q = 1) : d158917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14594, d158917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34573 q ha hb
    | true =>
      simp only [d14594, d158917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34574 q ha hb
  have h16 (q : Pattern) (ha : d14595 q = 1) (hb : d122305 q = 1) : d158918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14595, d158918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14595, d158918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14596 q = 1) (hb : d122305 q = 1) : d158919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14596, d158919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14596, d158919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14597 q = 1) (hb : d122305 q = 1) : d158920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14597, d158920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14597, d158920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14600 q = 1) (hb : d122305 q = 1) : d158922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14600, d158922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34575 q ha hb
    | true =>
      simp only [d14600, d158922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34576 q ha hb
  have h20 (q : Pattern) (ha : d14601 q = 1) (hb : d122305 q = 1) : d158923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14601, d158923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14601, d158923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14602 q = 1) (hb : d122305 q = 1) : d158924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14602, d158924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14602, d158924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14604 q = 1) (hb : d122305 q = 1) : d158926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34577 q ha hb
    | true =>
      simp only [d14604, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34553 q ha hb
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125535 q = 1) : d158927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125535, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14610 q = 1) (hb : d122305 q = 1) : d158929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34578 q ha hb
    | true =>
      simp only [d14610, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14611 q = 1) (hb : d122305 q = 1) : d158930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14611, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122305 q = 1) (hb : d125536 q = 1) : d158931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125536, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122305 q = 1) (hb : d125537 q = 1) : d158932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, d158932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125537, d158932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122305 q = 1) (hb : d125538 q = 1) : d158933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, d158933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125538, d158933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122305 q = 1) (hb : d125539 q = 1) : d158934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, d158934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125539, d158934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34580 (p : Pattern) (ha : d122305 p = 1) (hb : d125546 p = 1) : d158943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14604 q = 1) (hb : d122305 q = 1) : d158926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34577 q ha hb
    | true =>
      simp only [d14604, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34553 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125535 q = 1) : d158927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125535, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14610 q = 1) (hb : d122305 q = 1) : d158929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34578 q ha hb
    | true =>
      simp only [d14610, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14611 q = 1) (hb : d122305 q = 1) : d158930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14611, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125536 q = 1) : d158931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125536, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125544 q = 1) : d158941 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, d158941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125544, d158941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125545 q = 1) : d158942 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, d158942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125545, d158942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125546 q = 1) : d158943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, d158943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125546, d158943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34581 (p : Pattern) (ha : d14649 p = 1) (hb : d122305 p = 1) : d124376 p = 1 := by
  have h0 (q : Pattern) (ha : d14643 q = 1) (hb : d122304 q = 1) : d14643 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14649 q = 1) (hb : d122305 q = 1) : d124376 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14649, d122305, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14649, d122305, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34582 (p : Pattern) (ha : d14653 p = 1) (hb : d122305 p = 1) : d158949 p = 1 := by
  have h0 (q : Pattern) (ha : d14371 q = 1) (hb : d122304 q = 1) : d14371 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14653 q = 1) (hb : d122305 q = 1) : d158949 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14653, d122305, d158949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14653, d122305, d158949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34583 (p : Pattern) (ha : d14667 p = 1) (hb : d122305 p = 1) : d158956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14650 q = 1) (hb : d122305 q = 1) : d124377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14650, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34581 q ha hb
    | true =>
      simp only [d14650, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
  have h2 (q : Pattern) (ha : d14651 q = 1) (hb : d122305 q = 1) : d124378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14651, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14651, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14652 q = 1) (hb : d122305 q = 1) : d124379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14652, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14652, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14654 q = 1) (hb : d122305 q = 1) : d158950 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14654, d158950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14654, d158950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34582 q ha hb
  have h5 (q : Pattern) (ha : d14655 q = 1) (hb : d122305 q = 1) : d158951 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14655, d158951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14655, d158951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14656 q = 1) (hb : d122305 q = 1) : d158952 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14656, d158952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14656, d158952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14657 q = 1) (hb : d122305 q = 1) : d158953 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14657, d158953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14657, d158953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14659 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
  have h9 (q : Pattern) (ha : d14660 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14661 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14662 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
    | true =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14663 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14664 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14665 q = 1) (hb : d122305 q = 1) : d158954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14665, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14666 q = 1) (hb : d122305 q = 1) : d158955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14666, d158955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14666, d158955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14667 q = 1) (hb : d122305 q = 1) : d158956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14667, d158956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14667, d158956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro34584 (p : Pattern) (ha : d14672 p = 1) (hb : d122305 p = 1) : d158960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14659 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
  have h2 (q : Pattern) (ha : d14660 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14661 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14662 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
    | true =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14663 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14664 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14665 q = 1) (hb : d122305 q = 1) : d158954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14665, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14670 q = 1) (hb : d122305 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14670, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14671 q = 1) (hb : d122305 q = 1) : d158959 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14671, d158959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14671, d158959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14672 q = 1) (hb : d122305 q = 1) : d158960 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14672, d158960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14672, d158960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro34585 (p : Pattern) (ha : d14678 p = 1) (hb : d122305 p = 1) : d158966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14668 q = 1) (hb : d122305 q = 1) : d158957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14668, d158957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34583 q ha hb
    | true =>
      simp only [d14668, d158957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14669 q = 1) (hb : d122305 q = 1) : d158958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14669, d158958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14669, d158958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14673 q = 1) (hb : d122305 q = 1) : d158961 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34584 q ha hb
    | true =>
      simp only [d14673, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14674 q = 1) (hb : d122305 q = 1) : d158962 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14675 q = 1) (hb : d122305 q = 1) : d158963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14675, d158963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14675, d158963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14676 q = 1) (hb : d122305 q = 1) : d158964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14676, d158964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14676, d158964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14677 q = 1) (hb : d122305 q = 1) : d158965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14677, d158965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14677, d158965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14678 q = 1) (hb : d122305 q = 1) : d158966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14678, d158966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14678, d158966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34586 (p : Pattern) (ha : d14686 p = 1) (hb : d122305 p = 1) : d158970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d122305 q = 1) : d158961 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34584 q ha hb
    | true =>
      simp only [d14673, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d122305 q = 1) : d158962 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14681 q = 1) (hb : d122305 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34560 q ha hb
    | true =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14682 q = 1) (hb : d122305 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14683 q = 1) (hb : d122305 q = 1) : d158967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14683, d158967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14683, d158967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14684 q = 1) (hb : d122305 q = 1) : d158968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14684, d158968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14684, d158968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14685 q = 1) (hb : d122305 q = 1) : d158969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14685, d158969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14685, d158969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14686 q = 1) (hb : d122305 q = 1) : d158970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14686, d158970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14686, d158970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34587 (p : Pattern) (ha : d14725 p = 1) (hb : d122305 p = 1) : d158976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d122305 q = 1) : d158961 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34584 q ha hb
    | true =>
      simp only [d14673, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d122305 q = 1) : d158962 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14722 q = 1) (hb : d122305 q = 1) : d158973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14722, d158973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14722, d158973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14723 q = 1) (hb : d122305 q = 1) : d158974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14723, d158974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14723, d158974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14724 q = 1) (hb : d122305 q = 1) : d158975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14724, d158975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14724, d158975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14725 q = 1) (hb : d122305 q = 1) : d158976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14725, d158976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14725, d158976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34588 (p : Pattern) (ha : d122305 p = 1) (hb : d125556 p = 1) : d158982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14687 q = 1) (hb : d122305 q = 1) : d158971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14687, d158971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34585 q ha hb
    | true =>
      simp only [d14687, d158971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34586 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125552 q = 1) : d158972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, d158972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125552, d158972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14726 q = 1) (hb : d122305 q = 1) : d158977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14726, d158977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34587 q ha hb
    | true =>
      simp only [d14726, d158977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14727 q = 1) (hb : d122305 q = 1) : d158978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14727, d158978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14727, d158978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125553 q = 1) : d158979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, d158979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125553, d158979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125554 q = 1) : d158980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, d158980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125554, d158980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125555 q = 1) : d158981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, d158981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125555, d158981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125556 q = 1) : d158982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, d158982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125556, d158982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34589 (p : Pattern) (ha : d122305 p = 1) (hb : d125562 p = 1) : d158988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14498 q = 1) (hb : d122305 q = 1) : d158867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14498, d158867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14498, d158867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34552 q ha hb
  have h2 (q : Pattern) (ha : d14499 q = 1) (hb : d122305 q = 1) : d158868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14499, d158868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14499, d158868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14508 q = 1) (hb : d122305 q = 1) : d158876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34552 q ha hb
    | true =>
      simp only [d14508, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34555 q ha hb
  have h4 (q : Pattern) (ha : d14509 q = 1) (hb : d122305 q = 1) : d158877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14509, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14510 q = 1) (hb : d122305 q = 1) : d158878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14510, d158878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14510, d158878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125540 q = 1) : d158935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, d158935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34572 q ha hb
    | true =>
      simp only [d125540, d158935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34579 q ha hb
  have h7 (q : Pattern) (ha : d14629 q = 1) (hb : d122305 q = 1) : d158937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14629, d158937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34556 q ha hb
    | true =>
      simp only [d14629, d158937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34557 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125541 q = 1) : d158938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, d158938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125541, d158938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125542 q = 1) : d158939 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, d158939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125542, d158939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125543 q = 1) : d158940 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, d158940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125543, d158940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125547 q = 1) : d158944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, d158944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125547, d158944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34580 q ha hb
  have h12 (q : Pattern) (ha : d14638 q = 1) (hb : d122305 q = 1) : d124371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14638, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14638, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34558 q ha hb
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125548 q = 1) : d158945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, d158945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125548, d158945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125549 q = 1) : d158946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, d158946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125549, d158946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125550 q = 1) : d158947 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, d158947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125550, d158947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125551 q = 1) : d158948 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, d158948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125551, d158948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125557 q = 1) : d158983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, d158983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125557, d158983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34588 q ha hb
  have h18 (q : Pattern) (ha : d14743 q = 1) (hb : d122305 q = 1) : d124428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14743, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14743, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34562 q ha hb
  have h19 (q : Pattern) (ha : d122305 q = 1) (hb : d125558 q = 1) : d158984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, d158984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125558, d158984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122305 q = 1) (hb : d125559 q = 1) : d158985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, d158985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125559, d158985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122305 q = 1) (hb : d125560 q = 1) : d158986 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, d158986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125560, d158986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122305 q = 1) (hb : d125561 q = 1) : d158987 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, d158987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125561, d158987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125562 q = 1) : d158988 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, d158988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125562, d158988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34590 (p : Pattern) (ha : d122305 p = 1) (hb : d125568 p = 1) : d158994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d125563 q = 1) : d158989 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, d158989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125563, d158989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34589 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125564 q = 1) : d158990 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, d158990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125564, d158990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125565 q = 1) : d158991 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, d158991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125565, d158991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d125566 q = 1) : d158992 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, d158992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125566, d158992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125567 q = 1) : d158993 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, d158993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125567, d158993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125568 q = 1) : d158994 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, d158994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125568, d158994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34591 (p : Pattern) (ha : d14761 p = 1) (hb : d122305 p = 1) : d124442 p = 1 := by
  have h0 (q : Pattern) (ha : d14757 q = 1) (hb : d122304 q = 1) : d14757 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14761 q = 1) (hb : d122305 q = 1) : d124442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14761, d122305, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14761, d122305, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34592 (p : Pattern) (ha : d14766 p = 1) (hb : d122305 p = 1) : d124443 p = 1 := by
  have h0 (q : Pattern) (ha : d14762 q = 1) (hb : d122304 q = 1) : d14762 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14766 q = 1) (hb : d122305 q = 1) : d124443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14766, d122305, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14766, d122305, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34593 (p : Pattern) (ha : d14773 p = 1) (hb : d122305 p = 1) : d5023 p = 1 := by
  have h0 (q : Pattern) (ha : d5022 q = 1) (hb : d122304 q = 1) : d5022 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14773 q = 1) (hb : d122305 q = 1) : d5023 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d122305, d5023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14773, d122305, d5023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34594 (p : Pattern) (ha : d14778 p = 1) (hb : d122305 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d1127 q = 1) (hb : d122304 q = 1) : d1127 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14778 q = 1) (hb : d122305 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d122305, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14778, d122305, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34595 (p : Pattern) (ha : d14784 p = 1) (hb : d122305 p = 1) : d158999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14774 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34593 q ha hb
  have h5 (q : Pattern) (ha : d14775 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14776 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14777 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14779 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34594 q ha hb
  have h9 (q : Pattern) (ha : d14780 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14781 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14782 q = 1) (hb : d122305 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14782, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14783 q = 1) (hb : d122305 q = 1) : d158998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14783, d158998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14783, d158998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14784 q = 1) (hb : d122305 q = 1) : d158999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14784, d158999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14784, d158999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34596 (p : Pattern) (ha : d14788 p = 1) (hb : d122305 p = 1) : d124457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14779 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34594 q ha hb
  have h2 (q : Pattern) (ha : d14780 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14781 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14782 q = 1) (hb : d122305 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14782, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14787 q = 1) (hb : d122305 q = 1) : d124456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14787, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14787, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14788 q = 1) (hb : d122305 q = 1) : d124457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14788, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14788, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34597 (p : Pattern) (ha : d14794 p = 1) (hb : d122305 p = 1) : d159005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34595 q ha hb
    | true =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d122305 q = 1) : d159004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14794 q = 1) (hb : d122305 q = 1) : d159005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14794, d159005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14794, d159005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34598 (p : Pattern) (ha : d14798 p = 1) (hb : d122305 p = 1) : d124467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d122305 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14798 q = 1) (hb : d122305 q = 1) : d124467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14798, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14798, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34599 (p : Pattern) (ha : d14804 p = 1) (hb : d122305 p = 1) : d159011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d122305 q = 1) : d159006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34597 q ha hb
    | true =>
      simp only [d14799, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34598 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d122305 q = 1) : d159007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d122305 q = 1) : d159008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d122305 q = 1) : d159009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d122305 q = 1) : d159010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14804 q = 1) (hb : d122305 q = 1) : d159011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34600 (p : Pattern) (ha : d14807 p = 1) (hb : d122305 p = 1) : d159014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34595 q ha hb
    | true =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d122305 q = 1) : d159004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14807 q = 1) (hb : d122305 q = 1) : d159014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14807, d159014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14807, d159014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34601 (p : Pattern) (ha : d14808 p = 1) (hb : d122305 p = 1) : d124477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d122305 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14808 q = 1) (hb : d122305 q = 1) : d124477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14808, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14808, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34602 (p : Pattern) (ha : d14814 p = 1) (hb : d122305 p = 1) : d159020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d122305 q = 1) : d159006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34597 q ha hb
    | true =>
      simp only [d14799, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34598 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d122305 q = 1) : d159007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d122305 q = 1) : d159008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d122305 q = 1) : d159009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d122305 q = 1) : d159010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14809 q = 1) (hb : d122305 q = 1) : d159015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34600 q ha hb
    | true =>
      simp only [d14809, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34601 q ha hb
  have h7 (q : Pattern) (ha : d14810 q = 1) (hb : d122305 q = 1) : d159016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14811 q = 1) (hb : d122305 q = 1) : d159017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14811, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14812 q = 1) (hb : d122305 q = 1) : d159018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14813 q = 1) (hb : d122305 q = 1) : d159019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14814 q = 1) (hb : d122305 q = 1) : d159020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14814, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34603 (p : Pattern) (ha : d14855 p = 1) (hb : d122305 p = 1) : d159046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14774 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34593 q ha hb
  have h5 (q : Pattern) (ha : d14775 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14776 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14777 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14853 q = 1) (hb : d122305 q = 1) : d124516 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14853, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14853, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14854 q = 1) (hb : d122305 q = 1) : d159045 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14854, d159045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14854, d159045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14855 q = 1) (hb : d122305 q = 1) : d159046 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14855, d159046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14855, d159046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34604 (p : Pattern) (ha : d14865 p = 1) (hb : d122305 p = 1) : d159056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34603 q ha hb
    | true =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d122305 q = 1) : d159053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d122305 q = 1) : d159054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d122305 q = 1) : d159055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14865 q = 1) (hb : d122305 q = 1) : d159056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14865, d159056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14865, d159056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34605 (p : Pattern) (ha : d14965 p = 1) (hb : d122305 p = 1) : d159095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14955 q = 1) (hb : d122305 q = 1) : d159090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14955, d159090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34604 q ha hb
    | true =>
      simp only [d14955, d159090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34598 q ha hb
  have h2 (q : Pattern) (ha : d14956 q = 1) (hb : d122305 q = 1) : d159091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14956, d159091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14956, d159091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14957 q = 1) (hb : d122305 q = 1) : d159092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14957, d159092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14957, d159092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14958 q = 1) (hb : d122305 q = 1) : d159093 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14958, d159093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14958, d159093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14959 q = 1) (hb : d122305 q = 1) : d159094 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14959, d159094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14959, d159094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14960 q = 1) (hb : d122305 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34598 q ha hb
    | true =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14961 q = 1) (hb : d122305 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14962 q = 1) (hb : d122305 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14963 q = 1) (hb : d122305 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14964 q = 1) (hb : d122305 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14965 q = 1) (hb : d122305 q = 1) : d159095 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14965, d159095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14965, d159095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34606 (p : Pattern) (ha : d14971 p = 1) (hb : d122305 p = 1) : d124580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14960 q = 1) (hb : d122305 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34598 q ha hb
    | true =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14961 q = 1) (hb : d122305 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14962 q = 1) (hb : d122305 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14963 q = 1) (hb : d122305 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14964 q = 1) (hb : d122305 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14966 q = 1) (hb : d122305 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34601 q ha hb
    | true =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14967 q = 1) (hb : d122305 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14968 q = 1) (hb : d122305 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14969 q = 1) (hb : d122305 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14970 q = 1) (hb : d122305 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14971 q = 1) (hb : d122305 q = 1) : d124580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14971, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14971, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34607 (p : Pattern) (ha : d14980 p = 1) (hb : d122305 p = 1) : d124589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14966 q = 1) (hb : d122305 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34601 q ha hb
    | true =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14967 q = 1) (hb : d122305 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14968 q = 1) (hb : d122305 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14969 q = 1) (hb : d122305 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14970 q = 1) (hb : d122305 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14980 q = 1) (hb : d122305 q = 1) : d124589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14980, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14980, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34608 (p : Pattern) (ha : d15015 p = 1) (hb : d122305 p = 1) : d124601 p = 1 := by
  have h0 (q : Pattern) (ha : d15014 q = 1) (hb : d122304 q = 1) : d15014 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15015 q = 1) (hb : d122305 q = 1) : d124601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15015, d122305, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15015, d122305, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34609 (p : Pattern) (ha : d15042 p = 1) (hb : d122305 p = 1) : d13190 p = 1 := by
  have h0 (q : Pattern) (ha : d1400 q = 1) (hb : d122304 q = 1) : d1400 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15042 q = 1) (hb : d122305 q = 1) : d13190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d122305, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15042, d122305, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34610 (p : Pattern) (ha : d15048 p = 1) (hb : d122305 p = 1) : d124627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15043 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15043, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34609 q ha hb
  have h2 (q : Pattern) (ha : d15044 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15045 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15046 q = 1) (hb : d122305 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15046, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15047 q = 1) (hb : d122305 q = 1) : d124626 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15047, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15047, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15048 q = 1) (hb : d122305 q = 1) : d124627 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15048, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15048, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34611 (p : Pattern) (ha : d15128 p = 1) (hb : d122305 p = 1) : d124654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15049 q = 1) (hb : d122305 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34610 q ha hb
    | true =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15050 q = 1) (hb : d122305 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15125 q = 1) (hb : d122305 q = 1) : d124651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15125, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15125, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15126 q = 1) (hb : d122305 q = 1) : d124652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15126, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15126, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15127 q = 1) (hb : d122305 q = 1) : d124653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15127, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15127, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15128 q = 1) (hb : d122305 q = 1) : d124654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15128, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15128, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34612 (p : Pattern) (ha : d15134 p = 1) (hb : d122305 p = 1) : d124660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15129 q = 1) (hb : d122305 q = 1) : d124655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15129, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34611 q ha hb
    | true =>
      simp only [d15129, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15130 q = 1) (hb : d122305 q = 1) : d124656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15130, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15130, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15131 q = 1) (hb : d122305 q = 1) : d124657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15131, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15131, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15132 q = 1) (hb : d122305 q = 1) : d124658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15132, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15132, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15133 q = 1) (hb : d122305 q = 1) : d124659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15133, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15133, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15134 q = 1) (hb : d122305 q = 1) : d124660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15134, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15134, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34613 (p : Pattern) (ha : d14819 p = 1) (hb : d122305 p = 1) : d159025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34595 q ha hb
    | true =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d122305 q = 1) : d159024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14819 q = 1) (hb : d122305 q = 1) : d159025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14819, d159025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14819, d159025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34614 (p : Pattern) (ha : d14821 p = 1) (hb : d122305 p = 1) : d124490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d122305 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14821 q = 1) (hb : d122305 q = 1) : d124490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14821, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14821, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34615 (p : Pattern) (ha : d14828 p = 1) (hb : d122305 p = 1) : d159032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34595 q ha hb
    | true =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d122305 q = 1) : d159030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d122305 q = 1) : d159031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14828 q = 1) (hb : d122305 q = 1) : d159032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14828, d159032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14828, d159032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34616 (p : Pattern) (ha : d14831 p = 1) (hb : d122305 p = 1) : d124500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d122305 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d122305 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14831 q = 1) (hb : d122305 q = 1) : d124500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14831, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14831, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34617 (p : Pattern) (ha : d14839 p = 1) (hb : d122305 p = 1) : d124504 p = 1 := by
  have h0 (q : Pattern) (ha : d14835 q = 1) (hb : d122304 q = 1) : d14835 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14838 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14839 q = 1) (hb : d122305 q = 1) : d124504 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14839, d122305, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14839, d122305, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34618 (p : Pattern) (ha : d14844 p = 1) (hb : d122305 p = 1) : d159036 p = 1 := by
  have h0 (q : Pattern) (ha : d14843 q = 1) (hb : d122304 q = 1) : d14843 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14844 q = 1) (hb : d122305 q = 1) : d159036 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14844, d122305, d159036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14844, d122305, d159036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34619 (p : Pattern) (ha : d14850 p = 1) (hb : d122305 p = 1) : d159042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14840 q = 1) (hb : d122305 q = 1) : d124505 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14840, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34617 q ha hb
    | true =>
      simp only [d14840, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
  have h2 (q : Pattern) (ha : d14841 q = 1) (hb : d122305 q = 1) : d124506 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14841, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14841, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14842 q = 1) (hb : d122305 q = 1) : d124507 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14842, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14842, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14845 q = 1) (hb : d122305 q = 1) : d159037 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14845, d159037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14845, d159037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34618 q ha hb
  have h5 (q : Pattern) (ha : d14846 q = 1) (hb : d122305 q = 1) : d159038 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14846, d159038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14846, d159038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14847 q = 1) (hb : d122305 q = 1) : d159039 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14847, d159039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14847, d159039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14848 q = 1) (hb : d122305 q = 1) : d159040 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14848, d159040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14848, d159040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h9 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14774 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34593 q ha hb
  have h12 (q : Pattern) (ha : d14775 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14776 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14777 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14849 q = 1) (hb : d122305 q = 1) : d159041 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14849, d159041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14849, d159041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14850 q = 1) (hb : d122305 q = 1) : d159042 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14850, d159042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14850, d159042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34620 (p : Pattern) (ha : d14861 p = 1) (hb : d122305 p = 1) : d159052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d122305 q = 1) : d159043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34619 q ha hb
    | true =>
      simp only [d14851, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d122305 q = 1) : d159044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34603 q ha hb
    | true =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d122305 q = 1) : d159049 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d122305 q = 1) : d159050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d122305 q = 1) : d159051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14861 q = 1) (hb : d122305 q = 1) : d159052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14861, d159052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14861, d159052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34621 (p : Pattern) (ha : d14916 p = 1) (hb : d122305 p = 1) : d158999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14774 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34593 q ha hb
  have h5 (q : Pattern) (ha : d14775 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14776 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14777 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12961 q = 1) (hb : d122305 q = 1) : d12961 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14911 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14911, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14911, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14912 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14912, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14912, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14913 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14913, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14913, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14914 q = 1) (hb : d122305 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14914, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14914, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d14915 q = 1) (hb : d122305 q = 1) : d158998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14915, d158998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14915, d158998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14916 q = 1) (hb : d122305 q = 1) : d158999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14916, d158999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14916, d158999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro34622 (p : Pattern) (ha : d14922 p = 1) (hb : d122305 p = 1) : d159062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34621 q ha hb
    | true =>
      simp only [d14917, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d122305 q = 1) : d159059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d122305 q = 1) : d159060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d122305 q = 1) : d159061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14922 q = 1) (hb : d122305 q = 1) : d159062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14922, d159062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14922, d159062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34623 (p : Pattern) (ha : d122305 p = 1) (hb : d125575 p = 1) : d159068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d122305 q = 1) : d159026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34613 q ha hb
    | true =>
      simp only [d14822, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34614 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d122305 q = 1) : d159027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d122305 q = 1) : d159028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d122305 q = 1) : d159029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d122305 q = 1) : d159033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34615 q ha hb
    | true =>
      simp only [d14832, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34616 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d122305 q = 1) : d159034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d122305 q = 1) : d159035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d122305 q = 1) : d159057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34620 q ha hb
    | true =>
      simp only [d14866, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34604 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125571 q = 1) : d159058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125571, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d122305 q = 1) : d159063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34622 q ha hb
    | true =>
      simp only [d14923, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d122305 q = 1) : d159064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125572 q = 1) : d159065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125573 q = 1) : d159066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125573, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125574 q = 1) : d159067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125574, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125575 q = 1) : d159068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, d159068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125575, d159068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34624 (p : Pattern) (ha : d14929 p = 1) (hb : d122305 p = 1) : d159069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34595 q ha hb
    | true =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d122305 q = 1) : d159024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14929 q = 1) (hb : d122305 q = 1) : d159069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14929, d159069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14929, d159069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34625 (p : Pattern) (ha : d14930 p = 1) (hb : d122305 p = 1) : d124542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d122305 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14930 q = 1) (hb : d122305 q = 1) : d124542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14930, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14930, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34626 (p : Pattern) (ha : d14935 p = 1) (hb : d122305 p = 1) : d159074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34595 q ha hb
    | true =>
      simp only [d14785, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d122305 q = 1) : d159030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d122305 q = 1) : d159031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14935 q = 1) (hb : d122305 q = 1) : d159074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14935, d159074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14935, d159074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34627 (p : Pattern) (ha : d14936 p = 1) (hb : d122305 p = 1) : d124548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d122305 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d122305 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14936 q = 1) (hb : d122305 q = 1) : d124548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14936, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14936, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34628 (p : Pattern) (ha : d14940 p = 1) (hb : d122305 p = 1) : d159078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d122305 q = 1) : d159043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34619 q ha hb
    | true =>
      simp only [d14851, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d122305 q = 1) : d159044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34603 q ha hb
    | true =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d122305 q = 1) : d159049 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d122305 q = 1) : d159050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d122305 q = 1) : d159051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14940 q = 1) (hb : d122305 q = 1) : d159078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14940, d159078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14940, d159078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34629 (p : Pattern) (ha : d14941 p = 1) (hb : d122305 p = 1) : d159079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34603 q ha hb
    | true =>
      simp only [d14856, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34596 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d122305 q = 1) : d159053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d122305 q = 1) : d159054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d122305 q = 1) : d159055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14941 q = 1) (hb : d122305 q = 1) : d159079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14941, d159079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14941, d159079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34630 (p : Pattern) (ha : d14947 p = 1) (hb : d122305 p = 1) : d159082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34621 q ha hb
    | true =>
      simp only [d14917, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d122305 q = 1) : d159059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d122305 q = 1) : d159060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d122305 q = 1) : d159061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14947 q = 1) (hb : d122305 q = 1) : d159082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14947, d159082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14947, d159082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34631 (p : Pattern) (ha : d122305 p = 1) (hb : d125580 p = 1) : d159088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d122305 q = 1) : d159026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34613 q ha hb
    | true =>
      simp only [d14822, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34614 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d122305 q = 1) : d159027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d122305 q = 1) : d159028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d122305 q = 1) : d159029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d122305 q = 1) : d159033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34615 q ha hb
    | true =>
      simp only [d14832, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34616 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d122305 q = 1) : d159034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d122305 q = 1) : d159035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d122305 q = 1) : d159057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34620 q ha hb
    | true =>
      simp only [d14866, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34604 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125571 q = 1) : d159058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125571, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d122305 q = 1) : d159063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34622 q ha hb
    | true =>
      simp only [d14923, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d122305 q = 1) : d159064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125572 q = 1) : d159065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125573 q = 1) : d159066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125573, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125574 q = 1) : d159067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125574, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14931 q = 1) (hb : d122305 q = 1) : d159070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14931, d159070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34624 q ha hb
    | true =>
      simp only [d14931, d159070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34625 q ha hb
  have h16 (q : Pattern) (ha : d14932 q = 1) (hb : d122305 q = 1) : d159071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14932, d159071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14932, d159071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14933 q = 1) (hb : d122305 q = 1) : d159072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14933, d159072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14933, d159072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14934 q = 1) (hb : d122305 q = 1) : d159073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14934, d159073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14934, d159073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14937 q = 1) (hb : d122305 q = 1) : d159075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14937, d159075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34626 q ha hb
    | true =>
      simp only [d14937, d159075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34627 q ha hb
  have h20 (q : Pattern) (ha : d14938 q = 1) (hb : d122305 q = 1) : d159076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14938, d159076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14938, d159076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14939 q = 1) (hb : d122305 q = 1) : d159077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14939, d159077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14939, d159077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14942 q = 1) (hb : d122305 q = 1) : d159080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34628 q ha hb
    | true =>
      simp only [d14942, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34629 q ha hb
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125576 q = 1) : d159081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125576, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14948 q = 1) (hb : d122305 q = 1) : d159083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34630 q ha hb
    | true =>
      simp only [d14948, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14949 q = 1) (hb : d122305 q = 1) : d159084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14949, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122305 q = 1) (hb : d125577 q = 1) : d159085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125577, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122305 q = 1) (hb : d125578 q = 1) : d159086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, d159086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125578, d159086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122305 q = 1) (hb : d125579 q = 1) : d159087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, d159087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125579, d159087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122305 q = 1) (hb : d125580 q = 1) : d159088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, d159088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125580, d159088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34632 (p : Pattern) (ha : d122305 p = 1) (hb : d125587 p = 1) : d159102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14942 q = 1) (hb : d122305 q = 1) : d159080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34628 q ha hb
    | true =>
      simp only [d14942, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34629 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125576 q = 1) : d159081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125576, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14948 q = 1) (hb : d122305 q = 1) : d159083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34630 q ha hb
    | true =>
      simp only [d14948, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14949 q = 1) (hb : d122305 q = 1) : d159084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14949, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125577 q = 1) : d159085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125577, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125585 q = 1) : d159100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, d159100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125585, d159100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125586 q = 1) : d159101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, d159101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125586, d159101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125587 q = 1) : d159102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, d159102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125587, d159102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34633 (p : Pattern) (ha : d14992 p = 1) (hb : d122305 p = 1) : d124595 p = 1 := by
  have h0 (q : Pattern) (ha : d14986 q = 1) (hb : d122304 q = 1) : d14986 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14991 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14992 q = 1) (hb : d122305 q = 1) : d124595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14992, d122305, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14992, d122305, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34634 (p : Pattern) (ha : d14999 p = 1) (hb : d122305 p = 1) : d124596 p = 1 := by
  have h0 (q : Pattern) (ha : d14993 q = 1) (hb : d122304 q = 1) : d14993 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14998 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14999 q = 1) (hb : d122305 q = 1) : d124596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14999, d122305, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14999, d122305, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34635 (p : Pattern) (ha : d15009 p = 1) (hb : d122305 p = 1) : d159108 p = 1 := by
  have h0 (q : Pattern) (ha : d15003 q = 1) (hb : d122304 q = 1) : d15003 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15009 q = 1) (hb : d122305 q = 1) : d159108 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15009, d122305, d159108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15009, d122305, d159108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34636 (p : Pattern) (ha : d15024 p = 1) (hb : d122305 p = 1) : d6355 p = 1 := by
  have h0 (q : Pattern) (ha : d6354 q = 1) (hb : d122304 q = 1) : d6354 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15024 q = 1) (hb : d122305 q = 1) : d6355 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d122305, d6355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15024, d122305, d6355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34637 (p : Pattern) (ha : d15030 p = 1) (hb : d122305 p = 1) : d159115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15000 q = 1) (hb : d122305 q = 1) : d124597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15000, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34633 q ha hb
    | true =>
      simp only [d15000, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
  have h2 (q : Pattern) (ha : d15001 q = 1) (hb : d122305 q = 1) : d124598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15001, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15001, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15002 q = 1) (hb : d122305 q = 1) : d124599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15002, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15002, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15010 q = 1) (hb : d122305 q = 1) : d159109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15010, d159109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15010, d159109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34635 q ha hb
  have h5 (q : Pattern) (ha : d15011 q = 1) (hb : d122305 q = 1) : d159110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15011, d159110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15011, d159110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15012 q = 1) (hb : d122305 q = 1) : d159111 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15012, d159111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15012, d159111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15013 q = 1) (hb : d122305 q = 1) : d159112 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15013, d159112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15013, d159112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h9 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15025 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34636 q ha hb
  have h12 (q : Pattern) (ha : d15026 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15027 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15028 q = 1) (hb : d122305 q = 1) : d159113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15028, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15029 q = 1) (hb : d122305 q = 1) : d159114 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15029, d159114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15029, d159114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15030 q = 1) (hb : d122305 q = 1) : d159115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15030, d159115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15030, d159115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34638 (p : Pattern) (ha : d15035 p = 1) (hb : d122305 p = 1) : d159119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34636 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d122305 q = 1) : d159113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15033 q = 1) (hb : d122305 q = 1) : d124613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15033, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15033, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15034 q = 1) (hb : d122305 q = 1) : d159118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15034, d159118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15034, d159118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15035 q = 1) (hb : d122305 q = 1) : d159119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15035, d159119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15035, d159119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34639 (p : Pattern) (ha : d15041 p = 1) (hb : d122305 p = 1) : d159125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15031 q = 1) (hb : d122305 q = 1) : d159116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15031, d159116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34637 q ha hb
    | true =>
      simp only [d15031, d159116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15032 q = 1) (hb : d122305 q = 1) : d159117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15032, d159117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15032, d159117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15036 q = 1) (hb : d122305 q = 1) : d159120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34638 q ha hb
    | true =>
      simp only [d15036, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15037 q = 1) (hb : d122305 q = 1) : d159121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15038 q = 1) (hb : d122305 q = 1) : d159122 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15038, d159122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15038, d159122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15039 q = 1) (hb : d122305 q = 1) : d159123 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15039, d159123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15039, d159123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15040 q = 1) (hb : d122305 q = 1) : d159124 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15040, d159124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15040, d159124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15041 q = 1) (hb : d122305 q = 1) : d159125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15041, d159125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15041, d159125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34640 (p : Pattern) (ha : d15054 p = 1) (hb : d122305 p = 1) : d159129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15036 q = 1) (hb : d122305 q = 1) : d159120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34638 q ha hb
    | true =>
      simp only [d15036, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15037 q = 1) (hb : d122305 q = 1) : d159121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d122305 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34610 q ha hb
    | true =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d122305 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15051 q = 1) (hb : d122305 q = 1) : d159126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15051, d159126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15051, d159126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15052 q = 1) (hb : d122305 q = 1) : d159127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15052, d159127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15052, d159127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15053 q = 1) (hb : d122305 q = 1) : d159128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15053, d159128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15053, d159128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15054 q = 1) (hb : d122305 q = 1) : d159129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15054, d159129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15054, d159129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34641 (p : Pattern) (ha : d15111 p = 1) (hb : d122305 p = 1) : d159133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34636 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d122305 q = 1) : d159113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13190 q = 1) (hb : d122305 q = 1) : d13190 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15106 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15106, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15106, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15107 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15107, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15107, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15108 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15108, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15108, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15109 q = 1) (hb : d122305 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15109, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15109, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15110 q = 1) (hb : d122305 q = 1) : d159132 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15110, d159132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15110, d159132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15111 q = 1) (hb : d122305 q = 1) : d159133 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15111, d159133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15111, d159133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro34642 (p : Pattern) (ha : d15117 p = 1) (hb : d122305 p = 1) : d159139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15112 q = 1) (hb : d122305 q = 1) : d159134 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15112, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34641 q ha hb
    | true =>
      simp only [d15112, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15113 q = 1) (hb : d122305 q = 1) : d159135 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15113, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15113, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15114 q = 1) (hb : d122305 q = 1) : d159136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15114, d159136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15114, d159136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15115 q = 1) (hb : d122305 q = 1) : d159137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15115, d159137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15115, d159137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15116 q = 1) (hb : d122305 q = 1) : d159138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15116, d159138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15116, d159138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15117 q = 1) (hb : d122305 q = 1) : d159139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15117, d159139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15117, d159139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34643 (p : Pattern) (ha : d122305 p = 1) (hb : d125597 p = 1) : d159145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15055 q = 1) (hb : d122305 q = 1) : d159130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15055, d159130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34639 q ha hb
    | true =>
      simp only [d15055, d159130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34640 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125593 q = 1) : d159131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, d159131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125593, d159131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15118 q = 1) (hb : d122305 q = 1) : d159140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15118, d159140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34642 q ha hb
    | true =>
      simp only [d15118, d159140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15119 q = 1) (hb : d122305 q = 1) : d159141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15119, d159141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15119, d159141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125594 q = 1) : d159142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, d159142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125594, d159142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125595 q = 1) : d159143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, d159143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125595, d159143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125596 q = 1) : d159144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, d159144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125596, d159144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125597 q = 1) : d159145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, d159145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125597, d159145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34644 (p : Pattern) (ha : d122305 p = 1) (hb : d125603 p = 1) : d159151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14805 q = 1) (hb : d122305 q = 1) : d159012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14805, d159012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14805, d159012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34599 q ha hb
  have h2 (q : Pattern) (ha : d14806 q = 1) (hb : d122305 q = 1) : d159013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14806, d159013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14806, d159013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14815 q = 1) (hb : d122305 q = 1) : d159021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34599 q ha hb
    | true =>
      simp only [d14815, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34602 q ha hb
  have h4 (q : Pattern) (ha : d14816 q = 1) (hb : d122305 q = 1) : d159022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14816, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14817 q = 1) (hb : d122305 q = 1) : d159023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14817, d159023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14817, d159023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125581 q = 1) : d159089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, d159089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34623 q ha hb
    | true =>
      simp only [d125581, d159089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34631 q ha hb
  have h7 (q : Pattern) (ha : d14972 q = 1) (hb : d122305 q = 1) : d159096 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14972, d159096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34605 q ha hb
    | true =>
      simp only [d14972, d159096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34606 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125582 q = 1) : d159097 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, d159097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125582, d159097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125583 q = 1) : d159098 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, d159098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125583, d159098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125584 q = 1) : d159099 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, d159099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125584, d159099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125588 q = 1) : d159103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, d159103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125588, d159103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34632 q ha hb
  have h12 (q : Pattern) (ha : d14981 q = 1) (hb : d122305 q = 1) : d124590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14981, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14981, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34607 q ha hb
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125589 q = 1) : d159104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, d159104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125589, d159104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125590 q = 1) : d159105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, d159105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125590, d159105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125591 q = 1) : d159106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, d159106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125591, d159106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125592 q = 1) : d159107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, d159107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125592, d159107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125598 q = 1) : d159146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, d159146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125598, d159146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34643 q ha hb
  have h18 (q : Pattern) (ha : d15135 q = 1) (hb : d122305 q = 1) : d124661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15135, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15135, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34612 q ha hb
  have h19 (q : Pattern) (ha : d122305 q = 1) (hb : d125599 q = 1) : d159147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, d159147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125599, d159147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122305 q = 1) (hb : d125600 q = 1) : d159148 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, d159148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125600, d159148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122305 q = 1) (hb : d125601 q = 1) : d159149 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, d159149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125601, d159149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122305 q = 1) (hb : d125602 q = 1) : d159150 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, d159150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125602, d159150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125603 q = 1) : d159151 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, d159151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125603, d159151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34645 (p : Pattern) (ha : d122305 p = 1) (hb : d125609 p = 1) : d159157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d125604 q = 1) : d159152 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, d159152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125604, d159152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34644 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125605 q = 1) : d159153 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, d159153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125605, d159153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125606 q = 1) : d159154 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, d159154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125606, d159154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d125607 q = 1) : d159155 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, d159155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125607, d159155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125608 q = 1) : d159156 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, d159156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125608, d159156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125609 q = 1) : d159157 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, d159157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125609, d159157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34646 (p : Pattern) (ha : d15154 p = 1) (hb : d122305 p = 1) : d124676 p = 1 := by
  have h0 (q : Pattern) (ha : d15150 q = 1) (hb : d122304 q = 1) : d15150 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15154 q = 1) (hb : d122305 q = 1) : d124676 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15154, d122305, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15154, d122305, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34647 (p : Pattern) (ha : d15159 p = 1) (hb : d122305 p = 1) : d124677 p = 1 := by
  have h0 (q : Pattern) (ha : d15155 q = 1) (hb : d122304 q = 1) : d15155 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15159 q = 1) (hb : d122305 q = 1) : d124677 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15159, d122305, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15159, d122305, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34648 (p : Pattern) (ha : d15166 p = 1) (hb : d122305 p = 1) : d5139 p = 1 := by
  have h0 (q : Pattern) (ha : d5138 q = 1) (hb : d122304 q = 1) : d5138 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15166 q = 1) (hb : d122305 q = 1) : d5139 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d122305, d5139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15166, d122305, d5139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34649 (p : Pattern) (ha : d15171 p = 1) (hb : d122305 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d1588 q = 1) (hb : d122304 q = 1) : d1588 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15171 q = 1) (hb : d122305 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d122305, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15171, d122305, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34650 (p : Pattern) (ha : d15177 p = 1) (hb : d122305 p = 1) : d159163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34648 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15172 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34649 q ha hb
  have h9 (q : Pattern) (ha : d15173 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15174 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15175 q = 1) (hb : d122305 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15175, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15176 q = 1) (hb : d122305 q = 1) : d159162 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15176, d159162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15176, d159162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15177 q = 1) (hb : d122305 q = 1) : d159163 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15177, d159163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15177, d159163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34651 (p : Pattern) (ha : d15181 p = 1) (hb : d122305 p = 1) : d124691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15172 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34649 q ha hb
  have h2 (q : Pattern) (ha : d15173 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15174 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15175 q = 1) (hb : d122305 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15175, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15180 q = 1) (hb : d122305 q = 1) : d124690 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15180, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15180, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15181 q = 1) (hb : d122305 q = 1) : d124691 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15181, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15181, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34652 (p : Pattern) (ha : d15187 p = 1) (hb : d122305 p = 1) : d159169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34650 q ha hb
    | true =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d122305 q = 1) : d159168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15187 q = 1) (hb : d122305 q = 1) : d159169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15187, d159169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15187, d159169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34653 (p : Pattern) (ha : d15191 p = 1) (hb : d122305 p = 1) : d124701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d122305 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15191 q = 1) (hb : d122305 q = 1) : d124701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15191, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15191, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34654 (p : Pattern) (ha : d15197 p = 1) (hb : d122305 p = 1) : d159175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d122305 q = 1) : d159170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34652 q ha hb
    | true =>
      simp only [d15192, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34653 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d122305 q = 1) : d159171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d122305 q = 1) : d159172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d122305 q = 1) : d159173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d122305 q = 1) : d159174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15197 q = 1) (hb : d122305 q = 1) : d159175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34655 (p : Pattern) (ha : d15200 p = 1) (hb : d122305 p = 1) : d159178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34650 q ha hb
    | true =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d122305 q = 1) : d159168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15200 q = 1) (hb : d122305 q = 1) : d159178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15200, d159178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15200, d159178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34656 (p : Pattern) (ha : d15201 p = 1) (hb : d122305 p = 1) : d124711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d122305 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15201 q = 1) (hb : d122305 q = 1) : d124711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15201, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15201, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34657 (p : Pattern) (ha : d15207 p = 1) (hb : d122305 p = 1) : d159184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d122305 q = 1) : d159170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34652 q ha hb
    | true =>
      simp only [d15192, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34653 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d122305 q = 1) : d159171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d122305 q = 1) : d159172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d122305 q = 1) : d159173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d122305 q = 1) : d159174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15202 q = 1) (hb : d122305 q = 1) : d159179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34655 q ha hb
    | true =>
      simp only [d15202, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34656 q ha hb
  have h7 (q : Pattern) (ha : d15203 q = 1) (hb : d122305 q = 1) : d159180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15204 q = 1) (hb : d122305 q = 1) : d159181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15204, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15205 q = 1) (hb : d122305 q = 1) : d159182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15206 q = 1) (hb : d122305 q = 1) : d159183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15207 q = 1) (hb : d122305 q = 1) : d159184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15207, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34658 (p : Pattern) (ha : d15248 p = 1) (hb : d122305 p = 1) : d159210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34648 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15246 q = 1) (hb : d122305 q = 1) : d124750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15246, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15247 q = 1) (hb : d122305 q = 1) : d159209 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, d159209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15247, d159209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15248 q = 1) (hb : d122305 q = 1) : d159210 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, d159210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15248, d159210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34659 (p : Pattern) (ha : d15258 p = 1) (hb : d122305 p = 1) : d159220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d122305 q = 1) : d159211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34658 q ha hb
    | true =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d122305 q = 1) : d159212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d122305 q = 1) : d159217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d159217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d159217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d122305 q = 1) : d159218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d159218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d159218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d122305 q = 1) : d159219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d159219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d159219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15258 q = 1) (hb : d122305 q = 1) : d159220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, d159220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15258, d159220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34660 (p : Pattern) (ha : d15358 p = 1) (hb : d122305 p = 1) : d159259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15348 q = 1) (hb : d122305 q = 1) : d159254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, d159254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34659 q ha hb
    | true =>
      simp only [d15348, d159254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34653 q ha hb
  have h2 (q : Pattern) (ha : d15349 q = 1) (hb : d122305 q = 1) : d159255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, d159255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15349, d159255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15350 q = 1) (hb : d122305 q = 1) : d159256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, d159256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15350, d159256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15351 q = 1) (hb : d122305 q = 1) : d159257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, d159257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15351, d159257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15352 q = 1) (hb : d122305 q = 1) : d159258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, d159258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15352, d159258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15353 q = 1) (hb : d122305 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34653 q ha hb
    | true =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15354 q = 1) (hb : d122305 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15355 q = 1) (hb : d122305 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15356 q = 1) (hb : d122305 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15357 q = 1) (hb : d122305 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15358 q = 1) (hb : d122305 q = 1) : d159259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, d159259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15358, d159259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34661 (p : Pattern) (ha : d15364 p = 1) (hb : d122305 p = 1) : d124814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15353 q = 1) (hb : d122305 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34653 q ha hb
    | true =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15354 q = 1) (hb : d122305 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15355 q = 1) (hb : d122305 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15356 q = 1) (hb : d122305 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15357 q = 1) (hb : d122305 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15359 q = 1) (hb : d122305 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34656 q ha hb
    | true =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15360 q = 1) (hb : d122305 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15361 q = 1) (hb : d122305 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15362 q = 1) (hb : d122305 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15363 q = 1) (hb : d122305 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15364 q = 1) (hb : d122305 q = 1) : d124814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15364, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34662 (p : Pattern) (ha : d15373 p = 1) (hb : d122305 p = 1) : d124823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15359 q = 1) (hb : d122305 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34656 q ha hb
    | true =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15360 q = 1) (hb : d122305 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15361 q = 1) (hb : d122305 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15362 q = 1) (hb : d122305 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15363 q = 1) (hb : d122305 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15373 q = 1) (hb : d122305 q = 1) : d124823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15373, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34663 (p : Pattern) (ha : d15408 p = 1) (hb : d122305 p = 1) : d124835 p = 1 := by
  have h0 (q : Pattern) (ha : d15407 q = 1) (hb : d122304 q = 1) : d15407 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15408 q = 1) (hb : d122305 q = 1) : d124835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15408, d122305, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15408, d122305, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34664 (p : Pattern) (ha : d15435 p = 1) (hb : d122305 p = 1) : d13516 p = 1 := by
  have h0 (q : Pattern) (ha : d1877 q = 1) (hb : d122304 q = 1) : d1877 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15435 q = 1) (hb : d122305 q = 1) : d13516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d122305, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15435, d122305, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34665 (p : Pattern) (ha : d15441 p = 1) (hb : d122305 p = 1) : d124861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15436 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15436, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34664 q ha hb
  have h2 (q : Pattern) (ha : d15437 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15438 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15439 q = 1) (hb : d122305 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15439, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15440 q = 1) (hb : d122305 q = 1) : d124860 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15440, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15441 q = 1) (hb : d122305 q = 1) : d124861 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15441, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34666 (p : Pattern) (ha : d15521 p = 1) (hb : d122305 p = 1) : d124888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15442 q = 1) (hb : d122305 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34665 q ha hb
    | true =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15443 q = 1) (hb : d122305 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15518 q = 1) (hb : d122305 q = 1) : d124885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15518, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15519 q = 1) (hb : d122305 q = 1) : d124886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15519, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15520 q = 1) (hb : d122305 q = 1) : d124887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15520, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15521 q = 1) (hb : d122305 q = 1) : d124888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15521, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34667 (p : Pattern) (ha : d15527 p = 1) (hb : d122305 p = 1) : d124894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15522 q = 1) (hb : d122305 q = 1) : d124889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34666 q ha hb
    | true =>
      simp only [d15522, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15523 q = 1) (hb : d122305 q = 1) : d124890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15523, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15524 q = 1) (hb : d122305 q = 1) : d124891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15524, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15525 q = 1) (hb : d122305 q = 1) : d124892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15525, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15526 q = 1) (hb : d122305 q = 1) : d124893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15526, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15527 q = 1) (hb : d122305 q = 1) : d124894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15527, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34668 (p : Pattern) (ha : d15212 p = 1) (hb : d122305 p = 1) : d159189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34650 q ha hb
    | true =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d122305 q = 1) : d159188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d159188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d159188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15212 q = 1) (hb : d122305 q = 1) : d159189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15212, d159189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15212, d159189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34669 (p : Pattern) (ha : d15214 p = 1) (hb : d122305 p = 1) : d124724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d122305 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15214 q = 1) (hb : d122305 q = 1) : d124724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15214, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15214, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34670 (p : Pattern) (ha : d15221 p = 1) (hb : d122305 p = 1) : d159196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34650 q ha hb
    | true =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d122305 q = 1) : d159194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d159194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d159194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d122305 q = 1) : d159195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d159195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d159195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15221 q = 1) (hb : d122305 q = 1) : d159196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15221, d159196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15221, d159196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34671 (p : Pattern) (ha : d15224 p = 1) (hb : d122305 p = 1) : d124734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d122305 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d122305 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15224 q = 1) (hb : d122305 q = 1) : d124734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15224, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15224, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34672 (p : Pattern) (ha : d15232 p = 1) (hb : d122305 p = 1) : d124738 p = 1 := by
  have h0 (q : Pattern) (ha : d15228 q = 1) (hb : d122304 q = 1) : d15228 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15232 q = 1) (hb : d122305 q = 1) : d124738 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15232, d122305, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15232, d122305, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34673 (p : Pattern) (ha : d15237 p = 1) (hb : d122305 p = 1) : d159200 p = 1 := by
  have h0 (q : Pattern) (ha : d15236 q = 1) (hb : d122304 q = 1) : d15236 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15237 q = 1) (hb : d122305 q = 1) : d159200 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15237, d122305, d159200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15237, d122305, d159200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34674 (p : Pattern) (ha : d15243 p = 1) (hb : d122305 p = 1) : d159206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15233 q = 1) (hb : d122305 q = 1) : d124739 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15233, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34672 q ha hb
    | true =>
      simp only [d15233, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
  have h2 (q : Pattern) (ha : d15234 q = 1) (hb : d122305 q = 1) : d124740 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15234, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15234, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15235 q = 1) (hb : d122305 q = 1) : d124741 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15235, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15235, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15238 q = 1) (hb : d122305 q = 1) : d159201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15238, d159201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15238, d159201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34673 q ha hb
  have h5 (q : Pattern) (ha : d15239 q = 1) (hb : d122305 q = 1) : d159202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15239, d159202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15239, d159202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15240 q = 1) (hb : d122305 q = 1) : d159203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15240, d159203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15240, d159203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15241 q = 1) (hb : d122305 q = 1) : d159204 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15241, d159204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15241, d159204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h9 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15167 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34648 q ha hb
  have h12 (q : Pattern) (ha : d15168 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15169 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15170 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15242 q = 1) (hb : d122305 q = 1) : d159205 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15242, d159205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15242, d159205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15243 q = 1) (hb : d122305 q = 1) : d159206 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15243, d159206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15243, d159206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34675 (p : Pattern) (ha : d15254 p = 1) (hb : d122305 p = 1) : d159216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d122305 q = 1) : d159207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d159207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34674 q ha hb
    | true =>
      simp only [d15244, d159207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d122305 q = 1) : d159208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d159208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d159208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d122305 q = 1) : d159211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34658 q ha hb
    | true =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d122305 q = 1) : d159212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d122305 q = 1) : d159213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d159213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d159213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d122305 q = 1) : d159214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d159214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d159214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d122305 q = 1) : d159215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d159215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d159215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15254 q = 1) (hb : d122305 q = 1) : d159216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, d159216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15254, d159216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34676 (p : Pattern) (ha : d15309 p = 1) (hb : d122305 p = 1) : d159163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34648 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13287 q = 1) (hb : d122305 q = 1) : d13287 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15304 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15304, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15304, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15305 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15305, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15305, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15306 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15306, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15307 q = 1) (hb : d122305 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15307, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15308 q = 1) (hb : d122305 q = 1) : d159162 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, d159162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15308, d159162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15309 q = 1) (hb : d122305 q = 1) : d159163 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, d159163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15309, d159163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro34677 (p : Pattern) (ha : d15315 p = 1) (hb : d122305 p = 1) : d159226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34676 q ha hb
    | true =>
      simp only [d15310, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d122305 q = 1) : d159223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d159223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d159223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d122305 q = 1) : d159224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d159224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d159224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d122305 q = 1) : d159225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d159225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d159225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15315 q = 1) (hb : d122305 q = 1) : d159226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, d159226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15315, d159226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34678 (p : Pattern) (ha : d122305 p = 1) (hb : d125617 p = 1) : d159232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d122305 q = 1) : d159190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d159190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34668 q ha hb
    | true =>
      simp only [d15215, d159190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34669 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d122305 q = 1) : d159191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d159191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d159191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d122305 q = 1) : d159192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d159192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d159192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d122305 q = 1) : d159193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d159193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d159193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d122305 q = 1) : d159197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d159197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34670 q ha hb
    | true =>
      simp only [d15225, d159197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34671 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d122305 q = 1) : d159198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d159198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d159198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d122305 q = 1) : d159199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d159199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d159199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d122305 q = 1) : d159221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d159221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34675 q ha hb
    | true =>
      simp only [d15259, d159221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34659 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125613 q = 1) : d159222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d159222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125613, d159222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d122305 q = 1) : d159227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d159227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34677 q ha hb
    | true =>
      simp only [d15316, d159227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d122305 q = 1) : d159228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d159228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d159228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125614 q = 1) : d159229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d159229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d159229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125615 q = 1) : d159230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d159230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125615, d159230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125616 q = 1) : d159231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d159231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125616, d159231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125617 q = 1) : d159232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, d159232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125617, d159232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34679 (p : Pattern) (ha : d15322 p = 1) (hb : d122305 p = 1) : d159233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34650 q ha hb
    | true =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d122305 q = 1) : d159188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d159188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d159188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15322 q = 1) (hb : d122305 q = 1) : d159233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, d159233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15322, d159233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34680 (p : Pattern) (ha : d15323 p = 1) (hb : d122305 p = 1) : d124776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d122305 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15323 q = 1) (hb : d122305 q = 1) : d124776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15323, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34681 (p : Pattern) (ha : d15328 p = 1) (hb : d122305 p = 1) : d159238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34650 q ha hb
    | true =>
      simp only [d15178, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d122305 q = 1) : d159194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d159194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d159194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d122305 q = 1) : d159195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d159195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d159195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15328 q = 1) (hb : d122305 q = 1) : d159238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, d159238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15328, d159238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34682 (p : Pattern) (ha : d15329 p = 1) (hb : d122305 p = 1) : d124782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d122305 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d122305 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15329 q = 1) (hb : d122305 q = 1) : d124782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15329, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34683 (p : Pattern) (ha : d15333 p = 1) (hb : d122305 p = 1) : d159242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d122305 q = 1) : d159207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d159207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34674 q ha hb
    | true =>
      simp only [d15244, d159207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d122305 q = 1) : d159208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d159208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d159208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d122305 q = 1) : d159211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34658 q ha hb
    | true =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d122305 q = 1) : d159212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d122305 q = 1) : d159213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d159213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d159213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d122305 q = 1) : d159214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d159214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d159214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d122305 q = 1) : d159215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d159215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d159215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15333 q = 1) (hb : d122305 q = 1) : d159242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, d159242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15333, d159242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34684 (p : Pattern) (ha : d15334 p = 1) (hb : d122305 p = 1) : d159243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d122305 q = 1) : d159211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34658 q ha hb
    | true =>
      simp only [d15249, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d122305 q = 1) : d159212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34651 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d122305 q = 1) : d159217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d159217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d159217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d122305 q = 1) : d159218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d159218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d159218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d122305 q = 1) : d159219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d159219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d159219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15334 q = 1) (hb : d122305 q = 1) : d159243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, d159243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15334, d159243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34685 (p : Pattern) (ha : d15340 p = 1) (hb : d122305 p = 1) : d159246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34676 q ha hb
    | true =>
      simp only [d15310, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d122305 q = 1) : d159223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d159223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d159223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d122305 q = 1) : d159224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d159224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d159224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d122305 q = 1) : d159225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d159225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d159225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15340 q = 1) (hb : d122305 q = 1) : d159246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, d159246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15340, d159246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34686 (p : Pattern) (ha : d122305 p = 1) (hb : d125622 p = 1) : d159252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d122305 q = 1) : d159190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d159190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34668 q ha hb
    | true =>
      simp only [d15215, d159190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34669 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d122305 q = 1) : d159191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d159191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d159191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d122305 q = 1) : d159192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d159192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d159192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d122305 q = 1) : d159193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d159193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d159193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d122305 q = 1) : d159197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d159197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34670 q ha hb
    | true =>
      simp only [d15225, d159197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34671 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d122305 q = 1) : d159198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d159198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d159198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d122305 q = 1) : d159199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d159199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d159199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d122305 q = 1) : d159221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d159221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34675 q ha hb
    | true =>
      simp only [d15259, d159221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34659 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125613 q = 1) : d159222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d159222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125613, d159222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d122305 q = 1) : d159227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d159227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34677 q ha hb
    | true =>
      simp only [d15316, d159227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d122305 q = 1) : d159228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d159228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d159228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125614 q = 1) : d159229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d159229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d159229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125615 q = 1) : d159230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d159230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125615, d159230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125616 q = 1) : d159231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d159231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125616, d159231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15324 q = 1) (hb : d122305 q = 1) : d159234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, d159234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34679 q ha hb
    | true =>
      simp only [d15324, d159234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34680 q ha hb
  have h16 (q : Pattern) (ha : d15325 q = 1) (hb : d122305 q = 1) : d159235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, d159235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15325, d159235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15326 q = 1) (hb : d122305 q = 1) : d159236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, d159236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15326, d159236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15327 q = 1) (hb : d122305 q = 1) : d159237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, d159237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15327, d159237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15330 q = 1) (hb : d122305 q = 1) : d159239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, d159239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34681 q ha hb
    | true =>
      simp only [d15330, d159239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34682 q ha hb
  have h20 (q : Pattern) (ha : d15331 q = 1) (hb : d122305 q = 1) : d159240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, d159240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15331, d159240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15332 q = 1) (hb : d122305 q = 1) : d159241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, d159241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15332, d159241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15335 q = 1) (hb : d122305 q = 1) : d159244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d159244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34683 q ha hb
    | true =>
      simp only [d15335, d159244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34684 q ha hb
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125618 q = 1) : d159245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d159245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125618, d159245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d15341 q = 1) (hb : d122305 q = 1) : d159247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d159247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34685 q ha hb
    | true =>
      simp only [d15341, d159247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15342 q = 1) (hb : d122305 q = 1) : d159248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d159248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15342, d159248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122305 q = 1) (hb : d125619 q = 1) : d159249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d159249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125619, d159249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122305 q = 1) (hb : d125620 q = 1) : d159250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, d159250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125620, d159250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122305 q = 1) (hb : d125621 q = 1) : d159251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, d159251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125621, d159251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122305 q = 1) (hb : d125622 q = 1) : d159252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, d159252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125622, d159252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34687 (p : Pattern) (ha : d122305 p = 1) (hb : d125629 p = 1) : d159266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15335 q = 1) (hb : d122305 q = 1) : d159244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d159244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34683 q ha hb
    | true =>
      simp only [d15335, d159244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34684 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125618 q = 1) : d159245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d159245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125618, d159245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15341 q = 1) (hb : d122305 q = 1) : d159247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d159247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34685 q ha hb
    | true =>
      simp only [d15341, d159247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15342 q = 1) (hb : d122305 q = 1) : d159248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d159248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15342, d159248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125619 q = 1) : d159249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d159249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125619, d159249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125627 q = 1) : d159264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, d159264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125627, d159264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125628 q = 1) : d159265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, d159265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125628, d159265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125629 q = 1) : d159266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d159266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125629, d159266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34688 (p : Pattern) (ha : d15385 p = 1) (hb : d122305 p = 1) : d124829 p = 1 := by
  have h0 (q : Pattern) (ha : d15379 q = 1) (hb : d122304 q = 1) : d15379 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15385 q = 1) (hb : d122305 q = 1) : d124829 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15385, d122305, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15385, d122305, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34689 (p : Pattern) (ha : d15392 p = 1) (hb : d122305 p = 1) : d124830 p = 1 := by
  have h0 (q : Pattern) (ha : d15386 q = 1) (hb : d122304 q = 1) : d15386 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15392 q = 1) (hb : d122305 q = 1) : d124830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15392, d122305, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15392, d122305, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34690 (p : Pattern) (ha : d15402 p = 1) (hb : d122305 p = 1) : d159272 p = 1 := by
  have h0 (q : Pattern) (ha : d15396 q = 1) (hb : d122304 q = 1) : d15396 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15402 q = 1) (hb : d122305 q = 1) : d159272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15402, d122305, d159272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15402, d122305, d159272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34691 (p : Pattern) (ha : d15417 p = 1) (hb : d122305 p = 1) : d6501 p = 1 := by
  have h0 (q : Pattern) (ha : d6500 q = 1) (hb : d122304 q = 1) : d6500 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15417 q = 1) (hb : d122305 q = 1) : d6501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d122305, d6501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15417, d122305, d6501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34692 (p : Pattern) (ha : d15423 p = 1) (hb : d122305 p = 1) : d159279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15393 q = 1) (hb : d122305 q = 1) : d124831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15393, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34688 q ha hb
    | true =>
      simp only [d15393, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
  have h2 (q : Pattern) (ha : d15394 q = 1) (hb : d122305 q = 1) : d124832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15394, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15394, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15395 q = 1) (hb : d122305 q = 1) : d124833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15395, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15403 q = 1) (hb : d122305 q = 1) : d159273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15403, d159273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15403, d159273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34690 q ha hb
  have h5 (q : Pattern) (ha : d15404 q = 1) (hb : d122305 q = 1) : d159274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15404, d159274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15404, d159274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15405 q = 1) (hb : d122305 q = 1) : d159275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15405, d159275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15405, d159275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15406 q = 1) (hb : d122305 q = 1) : d159276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, d159276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15406, d159276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h9 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15418 q = 1) (hb : d122305 q = 1) : d124844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34691 q ha hb
  have h12 (q : Pattern) (ha : d15419 q = 1) (hb : d122305 q = 1) : d124845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15420 q = 1) (hb : d122305 q = 1) : d124846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15421 q = 1) (hb : d122305 q = 1) : d159277 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15421, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15422 q = 1) (hb : d122305 q = 1) : d159278 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, d159278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15422, d159278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15423 q = 1) (hb : d122305 q = 1) : d159279 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, d159279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15423, d159279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34693 (p : Pattern) (ha : d15428 p = 1) (hb : d122305 p = 1) : d159283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d122305 q = 1) : d124844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34691 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d122305 q = 1) : d124845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d122305 q = 1) : d124846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d122305 q = 1) : d159277 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15426 q = 1) (hb : d122305 q = 1) : d124847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15426, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15427 q = 1) (hb : d122305 q = 1) : d159282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, d159282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15427, d159282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15428 q = 1) (hb : d122305 q = 1) : d159283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, d159283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15428, d159283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34694 (p : Pattern) (ha : d15434 p = 1) (hb : d122305 p = 1) : d159289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15424 q = 1) (hb : d122305 q = 1) : d159280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, d159280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34692 q ha hb
    | true =>
      simp only [d15424, d159280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15425 q = 1) (hb : d122305 q = 1) : d159281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, d159281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15425, d159281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15429 q = 1) (hb : d122305 q = 1) : d159284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d159284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34693 q ha hb
    | true =>
      simp only [d15429, d159284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15430 q = 1) (hb : d122305 q = 1) : d159285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d159285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d159285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15431 q = 1) (hb : d122305 q = 1) : d159286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, d159286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15431, d159286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15432 q = 1) (hb : d122305 q = 1) : d159287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, d159287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15432, d159287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15433 q = 1) (hb : d122305 q = 1) : d159288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, d159288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15433, d159288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15434 q = 1) (hb : d122305 q = 1) : d159289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, d159289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15434, d159289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34695 (p : Pattern) (ha : d15447 p = 1) (hb : d122305 p = 1) : d159293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15429 q = 1) (hb : d122305 q = 1) : d159284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d159284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34693 q ha hb
    | true =>
      simp only [d15429, d159284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15430 q = 1) (hb : d122305 q = 1) : d159285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d159285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d159285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d122305 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34665 q ha hb
    | true =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d122305 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15444 q = 1) (hb : d122305 q = 1) : d159290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, d159290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15444, d159290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15445 q = 1) (hb : d122305 q = 1) : d159291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, d159291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15445, d159291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15446 q = 1) (hb : d122305 q = 1) : d159292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, d159292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15446, d159292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15447 q = 1) (hb : d122305 q = 1) : d159293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, d159293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15447, d159293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34696 (p : Pattern) (ha : d15504 p = 1) (hb : d122305 p = 1) : d159297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d122305 q = 1) : d124844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34691 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d122305 q = 1) : d124845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d122305 q = 1) : d124846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d122305 q = 1) : d159277 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13516 q = 1) (hb : d122305 q = 1) : d13516 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15499 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15499, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15499, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15500 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15500, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15500, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15501 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15501, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15502 q = 1) (hb : d122305 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15502, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15503 q = 1) (hb : d122305 q = 1) : d159296 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, d159296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15503, d159296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15504 q = 1) (hb : d122305 q = 1) : d159297 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, d159297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15504, d159297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro34697 (p : Pattern) (ha : d15510 p = 1) (hb : d122305 p = 1) : d159303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15505 q = 1) (hb : d122305 q = 1) : d159298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, d159298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34696 q ha hb
    | true =>
      simp only [d15505, d159298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15506 q = 1) (hb : d122305 q = 1) : d159299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, d159299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15506, d159299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15507 q = 1) (hb : d122305 q = 1) : d159300 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, d159300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15507, d159300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15508 q = 1) (hb : d122305 q = 1) : d159301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, d159301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15508, d159301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15509 q = 1) (hb : d122305 q = 1) : d159302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, d159302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15509, d159302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15510 q = 1) (hb : d122305 q = 1) : d159303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, d159303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15510, d159303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34698 (p : Pattern) (ha : d122305 p = 1) (hb : d125639 p = 1) : d159309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15448 q = 1) (hb : d122305 q = 1) : d159294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, d159294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34694 q ha hb
    | true =>
      simp only [d15448, d159294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34695 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125635 q = 1) : d159295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d159295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125635, d159295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15511 q = 1) (hb : d122305 q = 1) : d159304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, d159304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34697 q ha hb
    | true =>
      simp only [d15511, d159304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15512 q = 1) (hb : d122305 q = 1) : d159305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, d159305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15512, d159305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125636 q = 1) : d159306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d159306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125636, d159306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125637 q = 1) : d159307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d159307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125637, d159307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125638 q = 1) : d159308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d159308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125638, d159308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125639 q = 1) : d159309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d159309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125639, d159309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34699 (p : Pattern) (ha : d122305 p = 1) (hb : d125645 p = 1) : d159315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15198 q = 1) (hb : d122305 q = 1) : d159176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, d159176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15198, d159176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34654 q ha hb
  have h2 (q : Pattern) (ha : d15199 q = 1) (hb : d122305 q = 1) : d159177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, d159177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15199, d159177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15208 q = 1) (hb : d122305 q = 1) : d159185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34654 q ha hb
    | true =>
      simp only [d15208, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34657 q ha hb
  have h4 (q : Pattern) (ha : d15209 q = 1) (hb : d122305 q = 1) : d159186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15209, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15210 q = 1) (hb : d122305 q = 1) : d159187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, d159187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15210, d159187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125623 q = 1) : d159253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, d159253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34678 q ha hb
    | true =>
      simp only [d125623, d159253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34686 q ha hb
  have h7 (q : Pattern) (ha : d15365 q = 1) (hb : d122305 q = 1) : d159260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, d159260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34660 q ha hb
    | true =>
      simp only [d15365, d159260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34661 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125624 q = 1) : d159261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, d159261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125624, d159261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125625 q = 1) : d159262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d159262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125625, d159262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d125626 q = 1) : d159263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d159263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125626, d159263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d125630 q = 1) : d159267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d159267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125630, d159267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34687 q ha hb
  have h12 (q : Pattern) (ha : d15374 q = 1) (hb : d122305 q = 1) : d124824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15374, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34662 q ha hb
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125631 q = 1) : d159268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d159268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125631, d159268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125632 q = 1) : d159269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d159269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125632, d159269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125633 q = 1) : d159270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d159270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125633, d159270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d125634 q = 1) : d159271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d159271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125634, d159271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122305 q = 1) (hb : d125640 q = 1) : d159310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d159310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125640, d159310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34698 q ha hb
  have h18 (q : Pattern) (ha : d15528 q = 1) (hb : d122305 q = 1) : d124895 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15528, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34667 q ha hb
  have h19 (q : Pattern) (ha : d122305 q = 1) (hb : d125641 q = 1) : d159311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d159311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125641, d159311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122305 q = 1) (hb : d125642 q = 1) : d159312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d159312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125642, d159312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122305 q = 1) (hb : d125643 q = 1) : d159313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d159313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125643, d159313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122305 q = 1) (hb : d125644 q = 1) : d159314 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d159314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125644, d159314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125645 q = 1) : d159315 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d159315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125645, d159315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34700 (p : Pattern) (ha : d122305 p = 1) (hb : d125651 p = 1) : d159321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d125646 q = 1) : d159316 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d159316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125646, d159316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34699 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125647 q = 1) : d159317 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d159317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125647, d159317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d125648 q = 1) : d159318 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d159318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125648, d159318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d125649 q = 1) : d159319 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d159319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125649, d159319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125650 q = 1) : d159320 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d159320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125650, d159320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125651 q = 1) : d159321 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d159321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125651, d159321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34701 (p : Pattern) (ha : d15546 p = 1) (hb : d122305 p = 1) : d124911 p = 1 := by
  have h0 (q : Pattern) (ha : d15544 q = 1) (hb : d122304 q = 1) : d15544 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15546 q = 1) (hb : d122305 q = 1) : d124911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15546, d122305, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15546, d122305, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34702 (p : Pattern) (ha : d15551 p = 1) (hb : d122305 p = 1) : d124912 p = 1 := by
  have h0 (q : Pattern) (ha : d15547 q = 1) (hb : d122304 q = 1) : d15547 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15551 q = 1) (hb : d122305 q = 1) : d124912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15551, d122305, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15551, d122305, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34703 (p : Pattern) (ha : d15558 p = 1) (hb : d122305 p = 1) : d5252 p = 1 := by
  have h0 (q : Pattern) (ha : d5251 q = 1) (hb : d122304 q = 1) : d5251 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15558 q = 1) (hb : d122305 q = 1) : d5252 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d122305, d5252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15558, d122305, d5252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34704 (p : Pattern) (ha : d15563 p = 1) (hb : d122305 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d2071 q = 1) (hb : d122304 q = 1) : d2071 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15563 q = 1) (hb : d122305 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d122305, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15563, d122305, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34705 (p : Pattern) (ha : d15569 p = 1) (hb : d122305 p = 1) : d159328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d122305 q = 1) : d124981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34703 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d122305 q = 1) : d124982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d122305 q = 1) : d124983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d122305 q = 1) : d159326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15564 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34704 q ha hb
  have h9 (q : Pattern) (ha : d15565 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15566 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15567 q = 1) (hb : d122305 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15567, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15568 q = 1) (hb : d122305 q = 1) : d159327 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, d159327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15568, d159327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15569 q = 1) (hb : d122305 q = 1) : d159328 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, d159328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15569, d159328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34706 (p : Pattern) (ha : d15573 p = 1) (hb : d122305 p = 1) : d124926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15564 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34704 q ha hb
  have h2 (q : Pattern) (ha : d15565 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15566 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15567 q = 1) (hb : d122305 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15567, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15572 q = 1) (hb : d122305 q = 1) : d124925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15572, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15573 q = 1) (hb : d122305 q = 1) : d124926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15573, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34707 (p : Pattern) (ha : d15579 p = 1) (hb : d122305 p = 1) : d159334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34705 q ha hb
    | true =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122305 q = 1) : d159331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122305 q = 1) : d159332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d122305 q = 1) : d159333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d159333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d159333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15579 q = 1) (hb : d122305 q = 1) : d159334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, d159334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15579, d159334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34708 (p : Pattern) (ha : d15583 p = 1) (hb : d122305 p = 1) : d124936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122305 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122305 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d122305 q = 1) : d124935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15583 q = 1) (hb : d122305 q = 1) : d124936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15583, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34709 (p : Pattern) (ha : d15589 p = 1) (hb : d122305 p = 1) : d159340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d122305 q = 1) : d159335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34707 q ha hb
    | true =>
      simp only [d15584, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34708 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d122305 q = 1) : d159336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d122305 q = 1) : d159337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d122305 q = 1) : d159338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d122305 q = 1) : d159339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15589 q = 1) (hb : d122305 q = 1) : d159340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d159340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d159340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34710 (p : Pattern) (ha : d15592 p = 1) (hb : d122305 p = 1) : d159343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34705 q ha hb
    | true =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122305 q = 1) : d159331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122305 q = 1) : d159332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d122305 q = 1) : d159333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d159333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d159333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15592 q = 1) (hb : d122305 q = 1) : d159343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, d159343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15592, d159343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34711 (p : Pattern) (ha : d15593 p = 1) (hb : d122305 p = 1) : d124946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122305 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122305 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d122305 q = 1) : d124935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15593 q = 1) (hb : d122305 q = 1) : d124946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15593, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34712 (p : Pattern) (ha : d15599 p = 1) (hb : d122305 p = 1) : d159349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d122305 q = 1) : d159335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34707 q ha hb
    | true =>
      simp only [d15584, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34708 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d122305 q = 1) : d159336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d122305 q = 1) : d159337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d122305 q = 1) : d159338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d122305 q = 1) : d159339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15594 q = 1) (hb : d122305 q = 1) : d159344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34710 q ha hb
    | true =>
      simp only [d15594, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34711 q ha hb
  have h7 (q : Pattern) (ha : d15595 q = 1) (hb : d122305 q = 1) : d159345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15596 q = 1) (hb : d122305 q = 1) : d159346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15596, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15597 q = 1) (hb : d122305 q = 1) : d159347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15598 q = 1) (hb : d122305 q = 1) : d159348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15599 q = 1) (hb : d122305 q = 1) : d159349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d159349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15599, d159349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34713 (p : Pattern) (ha : d15636 p = 1) (hb : d122305 p = 1) : d159375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d122305 q = 1) : d124981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34703 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d122305 q = 1) : d124982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d122305 q = 1) : d124983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d122305 q = 1) : d159326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15634 q = 1) (hb : d122305 q = 1) : d124984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15634, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15635 q = 1) (hb : d122305 q = 1) : d159374 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, d159374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15635, d159374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15636 q = 1) (hb : d122305 q = 1) : d159375 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, d159375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15636, d159375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34714 (p : Pattern) (ha : d15646 p = 1) (hb : d122305 p = 1) : d159385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d122305 q = 1) : d159376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34713 q ha hb
    | true =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d122305 q = 1) : d159377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d122305 q = 1) : d159382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d159382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d159382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d122305 q = 1) : d159383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d159383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d159383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d122305 q = 1) : d159384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d159384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d159384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15646 q = 1) (hb : d122305 q = 1) : d159385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, d159385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15646, d159385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34715 (p : Pattern) (ha : d15746 p = 1) (hb : d122305 p = 1) : d159424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15736 q = 1) (hb : d122305 q = 1) : d159419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, d159419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34714 q ha hb
    | true =>
      simp only [d15736, d159419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34708 q ha hb
  have h2 (q : Pattern) (ha : d15737 q = 1) (hb : d122305 q = 1) : d159420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, d159420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15737, d159420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15738 q = 1) (hb : d122305 q = 1) : d159421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, d159421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15738, d159421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15739 q = 1) (hb : d122305 q = 1) : d159422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, d159422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15739, d159422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15740 q = 1) (hb : d122305 q = 1) : d159423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, d159423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15740, d159423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15741 q = 1) (hb : d122305 q = 1) : d125037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34708 q ha hb
    | true =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15742 q = 1) (hb : d122305 q = 1) : d125038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15743 q = 1) (hb : d122305 q = 1) : d125039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15744 q = 1) (hb : d122305 q = 1) : d125040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15745 q = 1) (hb : d122305 q = 1) : d125041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15746 q = 1) (hb : d122305 q = 1) : d159424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, d159424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15746, d159424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34716 (p : Pattern) (ha : d15752 p = 1) (hb : d122305 p = 1) : d125048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15741 q = 1) (hb : d122305 q = 1) : d125037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34708 q ha hb
    | true =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15742 q = 1) (hb : d122305 q = 1) : d125038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15743 q = 1) (hb : d122305 q = 1) : d125039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15744 q = 1) (hb : d122305 q = 1) : d125040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15745 q = 1) (hb : d122305 q = 1) : d125041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15747 q = 1) (hb : d122305 q = 1) : d125043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34711 q ha hb
    | true =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15748 q = 1) (hb : d122305 q = 1) : d125044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15749 q = 1) (hb : d122305 q = 1) : d125045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15750 q = 1) (hb : d122305 q = 1) : d125046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15751 q = 1) (hb : d122305 q = 1) : d125047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15752 q = 1) (hb : d122305 q = 1) : d125048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15752, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34717 (p : Pattern) (ha : d15761 p = 1) (hb : d122305 p = 1) : d125057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15747 q = 1) (hb : d122305 q = 1) : d125043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34711 q ha hb
    | true =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15748 q = 1) (hb : d122305 q = 1) : d125044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15749 q = 1) (hb : d122305 q = 1) : d125045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15750 q = 1) (hb : d122305 q = 1) : d125046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15751 q = 1) (hb : d122305 q = 1) : d125047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15761 q = 1) (hb : d122305 q = 1) : d125057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15761, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34718 (p : Pattern) (ha : d15786 p = 1) (hb : d122305 p = 1) : d125068 p = 1 := by
  have h0 (q : Pattern) (ha : d15785 q = 1) (hb : d122304 q = 1) : d15785 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15786 q = 1) (hb : d122305 q = 1) : d125068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15786, d122305, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15786, d122305, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34719 (p : Pattern) (ha : d15813 p = 1) (hb : d122305 p = 1) : d13843 p = 1 := by
  have h0 (q : Pattern) (ha : d2355 q = 1) (hb : d122304 q = 1) : d2355 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15813 q = 1) (hb : d122305 q = 1) : d13843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d122305, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15813, d122305, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34720 (p : Pattern) (ha : d15819 p = 1) (hb : d122305 p = 1) : d125094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15814 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15814, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34719 q ha hb
  have h2 (q : Pattern) (ha : d15815 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15816 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15817 q = 1) (hb : d122305 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15817, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15818 q = 1) (hb : d122305 q = 1) : d125093 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15818, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15819 q = 1) (hb : d122305 q = 1) : d125094 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15819, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34721 (p : Pattern) (ha : d15899 p = 1) (hb : d122305 p = 1) : d125121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15820 q = 1) (hb : d122305 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34720 q ha hb
    | true =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15821 q = 1) (hb : d122305 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15896 q = 1) (hb : d122305 q = 1) : d125118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15896, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15897 q = 1) (hb : d122305 q = 1) : d125119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15897, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15898 q = 1) (hb : d122305 q = 1) : d125120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15898, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15899 q = 1) (hb : d122305 q = 1) : d125121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15899, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34722 (p : Pattern) (ha : d15905 p = 1) (hb : d122305 p = 1) : d125127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15900 q = 1) (hb : d122305 q = 1) : d125122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34721 q ha hb
    | true =>
      simp only [d15900, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15901 q = 1) (hb : d122305 q = 1) : d125123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15901, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15902 q = 1) (hb : d122305 q = 1) : d125124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15902, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15903 q = 1) (hb : d122305 q = 1) : d125125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15903, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15904 q = 1) (hb : d122305 q = 1) : d125126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15904, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15905 q = 1) (hb : d122305 q = 1) : d125127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15905, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34723 (p : Pattern) (ha : d15604 p = 1) (hb : d122305 p = 1) : d159354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34705 q ha hb
    | true =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122305 q = 1) : d159331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122305 q = 1) : d159332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d122305 q = 1) : d159353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d159353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d159353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15604 q = 1) (hb : d122305 q = 1) : d159354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, d159354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15604, d159354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34724 (p : Pattern) (ha : d15606 p = 1) (hb : d122305 p = 1) : d124959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122305 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122305 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d122305 q = 1) : d124958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15606 q = 1) (hb : d122305 q = 1) : d124959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15606, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34725 (p : Pattern) (ha : d15613 p = 1) (hb : d122305 p = 1) : d159361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34705 q ha hb
    | true =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122305 q = 1) : d159331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d122305 q = 1) : d159359 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d159359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d159359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d122305 q = 1) : d159360 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d159360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d159360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15613 q = 1) (hb : d122305 q = 1) : d159361 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, d159361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15613, d159361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34726 (p : Pattern) (ha : d15616 p = 1) (hb : d122305 p = 1) : d124969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122305 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d122305 q = 1) : d124967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d122305 q = 1) : d124968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15616 q = 1) (hb : d122305 q = 1) : d124969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15616, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34727 (p : Pattern) (ha : d15625 p = 1) (hb : d122305 p = 1) : d159365 p = 1 := by
  have h0 (q : Pattern) (ha : d15545 q = 1) (hb : d122304 q = 1) : d15545 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15625 q = 1) (hb : d122305 q = 1) : d159365 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15625, d122305, d159365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15625, d122305, d159365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34728 (p : Pattern) (ha : d15631 p = 1) (hb : d122305 p = 1) : d159371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15621 q = 1) (hb : d122305 q = 1) : d15621 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15622 q = 1) (hb : d122305 q = 1) : d124973 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15622, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15622, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
  have h3 (q : Pattern) (ha : d15623 q = 1) (hb : d122305 q = 1) : d124974 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15623, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15623, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15624 q = 1) (hb : d122305 q = 1) : d124975 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15624, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15626 q = 1) (hb : d122305 q = 1) : d159366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15626, d159366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15626, d159366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34727 q ha hb
  have h6 (q : Pattern) (ha : d15627 q = 1) (hb : d122305 q = 1) : d159367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15627, d159367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15627, d159367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15628 q = 1) (hb : d122305 q = 1) : d159368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15628, d159368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15628, d159368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15629 q = 1) (hb : d122305 q = 1) : d159369 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, d159369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15629, d159369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h10 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15559 q = 1) (hb : d122305 q = 1) : d124981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34703 q ha hb
  have h13 (q : Pattern) (ha : d15560 q = 1) (hb : d122305 q = 1) : d124982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15561 q = 1) (hb : d122305 q = 1) : d124983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15562 q = 1) (hb : d122305 q = 1) : d159326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15630 q = 1) (hb : d122305 q = 1) : d159370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, d159370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15630, d159370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15631 q = 1) (hb : d122305 q = 1) : d159371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, d159371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15631, d159371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro34729 (p : Pattern) (ha : d15642 p = 1) (hb : d122305 p = 1) : d159381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d122305 q = 1) : d159372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d159372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34728 q ha hb
    | true =>
      simp only [d15632, d159372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d122305 q = 1) : d159373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d159373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d159373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d122305 q = 1) : d159376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34713 q ha hb
    | true =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d122305 q = 1) : d159377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d122305 q = 1) : d159378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d159378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d159378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d122305 q = 1) : d159379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d159379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d159379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d122305 q = 1) : d159380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d159380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d159380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15642 q = 1) (hb : d122305 q = 1) : d159381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, d159381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15642, d159381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34730 (p : Pattern) (ha : d15697 p = 1) (hb : d122305 p = 1) : d159328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d122305 q = 1) : d124981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34703 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d122305 q = 1) : d124982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d122305 q = 1) : d124983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d122305 q = 1) : d159326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d159326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13614 q = 1) (hb : d122305 q = 1) : d13614 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15692 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15692, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15692, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15693 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15693, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15693, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15694 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15694, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15695 q = 1) (hb : d122305 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15695, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15696 q = 1) (hb : d122305 q = 1) : d159327 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, d159327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15696, d159327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15697 q = 1) (hb : d122305 q = 1) : d159328 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, d159328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15697, d159328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro34731 (p : Pattern) (ha : d15703 p = 1) (hb : d122305 p = 1) : d159391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34730 q ha hb
    | true =>
      simp only [d15698, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d122305 q = 1) : d159388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d159388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d159388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d122305 q = 1) : d159389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d159389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d159389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d122305 q = 1) : d159390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d159390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d159390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15703 q = 1) (hb : d122305 q = 1) : d159391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, d159391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15703, d159391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34732 (p : Pattern) (ha : d122305 p = 1) (hb : d125660 p = 1) : d159397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d122305 q = 1) : d159355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d159355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34723 q ha hb
    | true =>
      simp only [d15607, d159355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34724 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d122305 q = 1) : d159356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d159356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d159356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d122305 q = 1) : d159357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d159357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d159357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d122305 q = 1) : d159358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d159358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d159358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d122305 q = 1) : d159362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d159362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34725 q ha hb
    | true =>
      simp only [d15617, d159362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34726 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d122305 q = 1) : d159363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d159363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d159363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d122305 q = 1) : d159364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d159364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d159364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d122305 q = 1) : d159386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d159386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34729 q ha hb
    | true =>
      simp only [d15647, d159386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34714 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125656 q = 1) : d159387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d159387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125656, d159387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d122305 q = 1) : d159392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d159392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34731 q ha hb
    | true =>
      simp only [d15704, d159392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d122305 q = 1) : d159393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d159393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d159393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125657 q = 1) : d159394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d159394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d159394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125658 q = 1) : d159395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d159395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125658, d159395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125659 q = 1) : d159396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d159396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125659, d159396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d125660 q = 1) : d159397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, d159397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125660, d159397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34733 (p : Pattern) (ha : d15710 p = 1) (hb : d122305 p = 1) : d159398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34705 q ha hb
    | true =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122305 q = 1) : d159331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122305 q = 1) : d159332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d159332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d122305 q = 1) : d159353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d159353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d159353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15710 q = 1) (hb : d122305 q = 1) : d159398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, d159398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15710, d159398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34734 (p : Pattern) (ha : d15711 p = 1) (hb : d122305 p = 1) : d125010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122305 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122305 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d122305 q = 1) : d124958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15711 q = 1) (hb : d122305 q = 1) : d125010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15711, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34735 (p : Pattern) (ha : d15716 p = 1) (hb : d122305 p = 1) : d159403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34705 q ha hb
    | true =>
      simp only [d15570, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122305 q = 1) : d159331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d159331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d122305 q = 1) : d159359 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d159359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d159359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d122305 q = 1) : d159360 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d159360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d159360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15716 q = 1) (hb : d122305 q = 1) : d159403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, d159403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15716, d159403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34736 (p : Pattern) (ha : d15717 p = 1) (hb : d122305 p = 1) : d125016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122305 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d122305 q = 1) : d124967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d122305 q = 1) : d124968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15717 q = 1) (hb : d122305 q = 1) : d125016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15717, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34737 (p : Pattern) (ha : d15721 p = 1) (hb : d122305 p = 1) : d159407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d122305 q = 1) : d159372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d159372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34728 q ha hb
    | true =>
      simp only [d15632, d159372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d122305 q = 1) : d159373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d159373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d159373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d122305 q = 1) : d159376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34713 q ha hb
    | true =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d122305 q = 1) : d159377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d122305 q = 1) : d159378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d159378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d159378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d122305 q = 1) : d159379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d159379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d159379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d122305 q = 1) : d159380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d159380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d159380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15721 q = 1) (hb : d122305 q = 1) : d159407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, d159407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15721, d159407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34738 (p : Pattern) (ha : d15722 p = 1) (hb : d122305 p = 1) : d159408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d122305 q = 1) : d159376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34713 q ha hb
    | true =>
      simp only [d15637, d159376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d122305 q = 1) : d159377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d159377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122305 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34706 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122305 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d122305 q = 1) : d159382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d159382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d159382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d122305 q = 1) : d159383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d159383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d159383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d122305 q = 1) : d159384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d159384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d159384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15722 q = 1) (hb : d122305 q = 1) : d159408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, d159408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15722, d159408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34739 (p : Pattern) (ha : d15728 p = 1) (hb : d122305 p = 1) : d159411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d122305 q = 1) : d159329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34730 q ha hb
    | true =>
      simp only [d15698, d159329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d122305 q = 1) : d159330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d159330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d122305 q = 1) : d159388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d159388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d159388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d122305 q = 1) : d159389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d159389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d159389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d122305 q = 1) : d159390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d159390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d159390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15728 q = 1) (hb : d122305 q = 1) : d159411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, d159411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15728, d159411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34740 (p : Pattern) (ha : d122305 p = 1) (hb : d125665 p = 1) : d159417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d122305 q = 1) : d159355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d159355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34723 q ha hb
    | true =>
      simp only [d15607, d159355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34724 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d122305 q = 1) : d159356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d159356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d159356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d122305 q = 1) : d159357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d159357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d159357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d122305 q = 1) : d159358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d159358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d159358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d122305 q = 1) : d159362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d159362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34725 q ha hb
    | true =>
      simp only [d15617, d159362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34726 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d122305 q = 1) : d159363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d159363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d159363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d122305 q = 1) : d159364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d159364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d159364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d122305 q = 1) : d159386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d159386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34729 q ha hb
    | true =>
      simp only [d15647, d159386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34714 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d125656 q = 1) : d159387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d159387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125656, d159387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d122305 q = 1) : d159392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d159392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34731 q ha hb
    | true =>
      simp only [d15704, d159392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d122305 q = 1) : d159393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d159393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d159393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d125657 q = 1) : d159394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d159394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d159394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d125658 q = 1) : d159395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d159395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125658, d159395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d125659 q = 1) : d159396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d159396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125659, d159396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15712 q = 1) (hb : d122305 q = 1) : d159399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, d159399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34733 q ha hb
    | true =>
      simp only [d15712, d159399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34734 q ha hb
  have h16 (q : Pattern) (ha : d15713 q = 1) (hb : d122305 q = 1) : d159400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, d159400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15713, d159400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15714 q = 1) (hb : d122305 q = 1) : d159401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, d159401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15714, d159401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15715 q = 1) (hb : d122305 q = 1) : d159402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, d159402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15715, d159402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15718 q = 1) (hb : d122305 q = 1) : d159404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, d159404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34735 q ha hb
    | true =>
      simp only [d15718, d159404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34736 q ha hb
  have h20 (q : Pattern) (ha : d15719 q = 1) (hb : d122305 q = 1) : d159405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, d159405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15719, d159405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15720 q = 1) (hb : d122305 q = 1) : d159406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, d159406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15720, d159406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15723 q = 1) (hb : d122305 q = 1) : d159409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34737 q ha hb
    | true =>
      simp only [d15723, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34738 q ha hb
  have h23 (q : Pattern) (ha : d122305 q = 1) (hb : d125661 q = 1) : d159410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125661, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d15729 q = 1) (hb : d122305 q = 1) : d159412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34739 q ha hb
    | true =>
      simp only [d15729, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15730 q = 1) (hb : d122305 q = 1) : d159413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15730, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122305 q = 1) (hb : d125662 q = 1) : d159414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125662, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122305 q = 1) (hb : d125663 q = 1) : d159415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, d159415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125663, d159415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122305 q = 1) (hb : d125664 q = 1) : d159416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, d159416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125664, d159416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122305 q = 1) (hb : d125665 q = 1) : d159417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, d159417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125665, d159417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34741 (p : Pattern) (ha : d122305 p = 1) (hb : d125672 p = 1) : d159431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15723 q = 1) (hb : d122305 q = 1) : d159409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34737 q ha hb
    | true =>
      simp only [d15723, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34738 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d125661 q = 1) : d159410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125661, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15729 q = 1) (hb : d122305 q = 1) : d159412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34739 q ha hb
    | true =>
      simp only [d15729, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15730 q = 1) (hb : d122305 q = 1) : d159413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15730, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d125662 q = 1) : d159414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125662, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d125670 q = 1) : d159429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, d159429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125670, d159429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d125671 q = 1) : d159430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, d159430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125671, d159430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d125672 q = 1) : d159431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d159431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125672, d159431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34742 (p : Pattern) (ha : d15771 p = 1) (hb : d122305 p = 1) : d125063 p = 1 := by
  have h0 (q : Pattern) (ha : d15769 q = 1) (hb : d122304 q = 1) : d15769 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15771 q = 1) (hb : d122305 q = 1) : d125063 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15771, d122305, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15771, d122305, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34743 (p : Pattern) (ha : d15780 p = 1) (hb : d122305 p = 1) : d159437 p = 1 := by
  have h0 (q : Pattern) (ha : d15770 q = 1) (hb : d122304 q = 1) : d15770 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15780 q = 1) (hb : d122305 q = 1) : d159437 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15780, d122305, d159437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15780, d122305, d159437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34744 (p : Pattern) (ha : d15795 p = 1) (hb : d122305 p = 1) : d6648 p = 1 := by
  have h0 (q : Pattern) (ha : d6647 q = 1) (hb : d122304 q = 1) : d6647 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15795 q = 1) (hb : d122305 q = 1) : d6648 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d122305, d6648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15795, d122305, d6648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro34745 (p : Pattern) (ha : d15801 p = 1) (hb : d122305 p = 1) : d159444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15768 q = 1) (hb : d122305 q = 1) : d15768 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15772 q = 1) (hb : d122305 q = 1) : d125064 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15772, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15772, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
  have h3 (q : Pattern) (ha : d15773 q = 1) (hb : d122305 q = 1) : d125065 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15773, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15773, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15774 q = 1) (hb : d122305 q = 1) : d125066 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15774, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15781 q = 1) (hb : d122305 q = 1) : d159438 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15781, d159438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15781, d159438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34743 q ha hb
  have h6 (q : Pattern) (ha : d15782 q = 1) (hb : d122305 q = 1) : d159439 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15782, d159439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15782, d159439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15783 q = 1) (hb : d122305 q = 1) : d159440 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15783, d159440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15783, d159440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15784 q = 1) (hb : d122305 q = 1) : d159441 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, d159441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15784, d159441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h10 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15796 q = 1) (hb : d122305 q = 1) : d125077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34744 q ha hb
  have h13 (q : Pattern) (ha : d15797 q = 1) (hb : d122305 q = 1) : d125078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15798 q = 1) (hb : d122305 q = 1) : d125079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15799 q = 1) (hb : d122305 q = 1) : d159442 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15799, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15800 q = 1) (hb : d122305 q = 1) : d159443 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, d159443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15800, d159443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15801 q = 1) (hb : d122305 q = 1) : d159444 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, d159444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15801, d159444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro34746 (p : Pattern) (ha : d15806 p = 1) (hb : d122305 p = 1) : d159448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d122305 q = 1) : d125077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34744 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d122305 q = 1) : d125078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d122305 q = 1) : d125079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d122305 q = 1) : d159442 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15804 q = 1) (hb : d122305 q = 1) : d125080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15804, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15805 q = 1) (hb : d122305 q = 1) : d159447 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, d159447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15805, d159447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15806 q = 1) (hb : d122305 q = 1) : d159448 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, d159448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15806, d159448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34747 (p : Pattern) (ha : d15812 p = 1) (hb : d122305 p = 1) : d159454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15802 q = 1) (hb : d122305 q = 1) : d159445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, d159445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34745 q ha hb
    | true =>
      simp only [d15802, d159445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15803 q = 1) (hb : d122305 q = 1) : d159446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, d159446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15803, d159446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15807 q = 1) (hb : d122305 q = 1) : d159449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34746 q ha hb
    | true =>
      simp only [d15807, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15808 q = 1) (hb : d122305 q = 1) : d159450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15809 q = 1) (hb : d122305 q = 1) : d159451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, d159451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15809, d159451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15810 q = 1) (hb : d122305 q = 1) : d159452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, d159452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15810, d159452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15811 q = 1) (hb : d122305 q = 1) : d159453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, d159453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15811, d159453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15812 q = 1) (hb : d122305 q = 1) : d159454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, d159454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15812, d159454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34748 (p : Pattern) (ha : d15825 p = 1) (hb : d122305 p = 1) : d159458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15807 q = 1) (hb : d122305 q = 1) : d159449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34746 q ha hb
    | true =>
      simp only [d15807, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15808 q = 1) (hb : d122305 q = 1) : d159450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d122305 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34720 q ha hb
    | true =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d122305 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15822 q = 1) (hb : d122305 q = 1) : d159455 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, d159455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15822, d159455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15823 q = 1) (hb : d122305 q = 1) : d159456 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, d159456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15823, d159456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15824 q = 1) (hb : d122305 q = 1) : d159457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, d159457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15824, d159457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15825 q = 1) (hb : d122305 q = 1) : d159458 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, d159458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15825, d159458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34749 (p : Pattern) (ha : d15882 p = 1) (hb : d122305 p = 1) : d159462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d122305 q = 1) : d125077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34744 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d122305 q = 1) : d125078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d122305 q = 1) : d125079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d122305 q = 1) : d159442 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13843 q = 1) (hb : d122305 q = 1) : d13843 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15877 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15877, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15877, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15878 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15878, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15878, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15879 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15879, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15880 q = 1) (hb : d122305 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15880, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15881 q = 1) (hb : d122305 q = 1) : d159461 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, d159461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15881, d159461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15882 q = 1) (hb : d122305 q = 1) : d159462 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, d159462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15882, d159462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
end NetHack.Soko22Hazard87
