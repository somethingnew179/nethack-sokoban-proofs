import NetHack.Soko22Hazard87.AndIntroBlocks0429
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro107500 (p : Pattern) (ha : d308 p = 1) (hb : d367655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d45542 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107361 q ha hb
    | true =>
      simp only [d45542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107362 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d45543 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d45544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d45545 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d45546 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107501 (p : Pattern) (ha : d308 p = 1) (hb : d367666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d367661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107402 q ha hb
    | true =>
      simp only [d367661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107370 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107502 (p : Pattern) (ha : d308 p = 1) (hb : d367672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d45548 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107360 q ha hb
    | true =>
      simp only [d45548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107363 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d45549 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107500 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d367658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d367659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d367660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d367667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107501 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d367668 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d367669 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d367670 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d367671 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d367672 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107503 (p : Pattern) (ha : d308 p = 1) (hb : d367678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d367673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107502 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107504 (p : Pattern) (ha : d308 p = 1) (hb : d367683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107421 q ha hb
    | true =>
      simp only [d46006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107422 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107505 (p : Pattern) (ha : d308 p = 1) (hb : d367694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d367689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107463 q ha hb
    | true =>
      simp only [d367689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107430 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107506 (p : Pattern) (ha : d308 p = 1) (hb : d367700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107420 q ha hb
    | true =>
      simp only [d46012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107423 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107504 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d367686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d367687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d367688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d367695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107505 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d367696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d367697 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d367698 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d367699 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d367700 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107507 (p : Pattern) (ha : d308 p = 1) (hb : d367706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d367701 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107506 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367702 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367703 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367704 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367705 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367706 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107508 (p : Pattern) (ha : d308 p = 1) (hb : d367712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107495 q ha hb
    | true =>
      simp only [d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107499 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107503 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107507 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107482 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107491 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d367711 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d367711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d367712 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d367712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d367712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro107509 (p : Pattern) (ha : d308 p = 1) (hb : d367718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d367713 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d367713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107508 q ha hb
    | true =>
      simp only [d367713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367714 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d367714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367715 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d367715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367716 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d367716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d367717 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d367717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d367718 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d367718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107510 (p : Pattern) (ha : d358929 p = 1) (hb : d367724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d367719 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107509 q ha hb
    | true =>
      simp only [d367719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d367720 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d367721 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d367722 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d358929 q = 1) (hb : d367723 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d358929, d367723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d358929, d367723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d358929 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d358929 q = 1) (hb : d367724 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro107511 (p : Pattern) (ha : d358929 p = 1) (hb : d367730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d358929 q = 1) (hb : d367725 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107510 q ha hb
    | true =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d358929 q = 1) (hb : d367726 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d358929 q = 1) (hb : d367727 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d358929 q = 1) (hb : d367728 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d358929 q = 1) (hb : d367729 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d358929 q = 1) (hb : d367730 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107512 (p : Pattern) (ha : d358929 p = 1) (hb : d367736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d358929 q = 1) (hb : d367731 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107511 q ha hb
    | true =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d358929 q = 1) (hb : d367732 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d358929 q = 1) (hb : d367733 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d358929 q = 1) (hb : d367734 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d358929 q = 1) (hb : d367735 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d358929 q = 1) (hb : d367736 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107513 (p : Pattern) (ha : d358929 p = 1) (hb : d367742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d358929 q = 1) (hb : d367737 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107512 q ha hb
    | true =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d358929 q = 1) (hb : d367738 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d358929 q = 1) (hb : d367739 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d358929 q = 1) (hb : d367740 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d358929 q = 1) (hb : d367741 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d358929 q = 1) (hb : d367742 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107514 (p : Pattern) (ha : d358929 p = 1) (hb : d367748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d358929 q = 1) (hb : d367743 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107513 q ha hb
    | true =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d358929 q = 1) (hb : d367744 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d358929 q = 1) (hb : d367745 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d358929 q = 1) (hb : d367746 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d358929 q = 1) (hb : d367747 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d358929 q = 1) (hb : d367748 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107515 (p : Pattern) (ha : d358929 p = 1) (hb : d367754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d358929 q = 1) (hb : d367749 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107514 q ha hb
    | true =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d358929 q = 1) (hb : d367750 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d358929 q = 1) (hb : d367751 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d358929 q = 1) (hb : d367752 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d358929 q = 1) (hb : d367753 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d358929 q = 1) (hb : d367754 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107516 (p : Pattern) (ha : d0 p = 1) (hb : d378986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378986 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107517 (p : Pattern) (ha : d322220 p = 1) (hb : d331330 p = 1) : d326435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322215 q = 1) (hb : d325306 q = 1) : d326430 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d322215, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104006 q ha hb
    | true =>
      simp only [d322215, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322216 q = 1) (hb : d325306 q = 1) : d326431 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d322216, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322216, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322217 q = 1) (hb : d325306 q = 1) : d326432 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d322217, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322217, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322218 q = 1) (hb : d325306 q = 1) : d326433 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322218, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d322219 q = 1) (hb : d331330 q = 1) : d326434 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d331330, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322219, d331330, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d322220 q = 1) (hb : d331330 q = 1) : d326435 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322220, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107518 (p : Pattern) (ha : d322226 p = 1) (hb : d331330 p = 1) : d326441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d331330 q = 1) : d326436 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107517 q ha hb
    | true =>
      simp only [d322221, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d331330 q = 1) : d326437 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d331330 q = 1) : d326438 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d331330 q = 1) : d326439 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d331330 q = 1) : d326440 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d331330 q = 1) : d326441 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107519 (p : Pattern) (ha : d322232 p = 1) (hb : d331330 p = 1) : d326447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d331330 q = 1) : d326442 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107518 q ha hb
    | true =>
      simp only [d322227, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d331330 q = 1) : d326443 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d331330 q = 1) : d326444 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d331330 q = 1) : d326445 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d331330 q = 1) : d326446 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d331330 q = 1) : d326447 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107520 (p : Pattern) (ha : d322238 p = 1) (hb : d331330 p = 1) : d326453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d331330 q = 1) : d326448 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107519 q ha hb
    | true =>
      simp only [d322233, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d331330 q = 1) : d326449 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d331330 q = 1) : d326450 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d331330 q = 1) : d326451 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d331330 q = 1) : d326452 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d331330 q = 1) : d326453 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107521 (p : Pattern) (ha : d322244 p = 1) (hb : d331330 p = 1) : d326459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d331330 q = 1) : d326454 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107520 q ha hb
    | true =>
      simp only [d322239, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d331330 q = 1) : d326455 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d331330 q = 1) : d326456 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d331330 q = 1) : d326457 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d331330 q = 1) : d326458 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d331330 q = 1) : d326459 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107522 (p : Pattern) (ha : d322250 p = 1) (hb : d331330 p = 1) : d326465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d331330 q = 1) : d326460 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107521 q ha hb
    | true =>
      simp only [d322245, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d331330 q = 1) : d326461 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d331330 q = 1) : d326462 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d331330 q = 1) : d326463 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d331330 q = 1) : d326464 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d331330 q = 1) : d326465 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107523 (p : Pattern) (ha : d331330 p = 1) (hb : d367724 p = 1) : d326635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367719 q = 1) : d326630 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104372 q ha hb
    | true =>
      simp only [d367719, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367720 q = 1) : d326631 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367721 q = 1) : d326632 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367722 q = 1) : d326633 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367722, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d331330 q = 1) (hb : d367723 q = 1) : d326634 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d331330, d367723, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331330, d367723, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d331330 q = 1) (hb : d367724 q = 1) : d326635 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367724, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro107524 (p : Pattern) (ha : d331330 p = 1) (hb : d367730 p = 1) : d326641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331330 q = 1) (hb : d367725 q = 1) : d326636 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107523 q ha hb
    | true =>
      simp only [d367725, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331330 q = 1) (hb : d367726 q = 1) : d326637 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331330 q = 1) (hb : d367727 q = 1) : d326638 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331330 q = 1) (hb : d367728 q = 1) : d326639 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331330 q = 1) (hb : d367729 q = 1) : d326640 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331330 q = 1) (hb : d367730 q = 1) : d326641 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107525 (p : Pattern) (ha : d331330 p = 1) (hb : d367736 p = 1) : d326647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331330 q = 1) (hb : d367731 q = 1) : d326642 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107524 q ha hb
    | true =>
      simp only [d367731, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331330 q = 1) (hb : d367732 q = 1) : d326643 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331330 q = 1) (hb : d367733 q = 1) : d326644 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331330 q = 1) (hb : d367734 q = 1) : d326645 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331330 q = 1) (hb : d367735 q = 1) : d326646 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331330 q = 1) (hb : d367736 q = 1) : d326647 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107526 (p : Pattern) (ha : d331330 p = 1) (hb : d367742 p = 1) : d326653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331330 q = 1) (hb : d367737 q = 1) : d326648 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107525 q ha hb
    | true =>
      simp only [d367737, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331330 q = 1) (hb : d367738 q = 1) : d326649 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331330 q = 1) (hb : d367739 q = 1) : d326650 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331330 q = 1) (hb : d367740 q = 1) : d326651 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331330 q = 1) (hb : d367741 q = 1) : d326652 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331330 q = 1) (hb : d367742 q = 1) : d326653 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107527 (p : Pattern) (ha : d331330 p = 1) (hb : d367748 p = 1) : d326659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331330 q = 1) (hb : d367743 q = 1) : d326654 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107526 q ha hb
    | true =>
      simp only [d367743, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331330 q = 1) (hb : d367744 q = 1) : d326655 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331330 q = 1) (hb : d367745 q = 1) : d326656 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331330 q = 1) (hb : d367746 q = 1) : d326657 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331330 q = 1) (hb : d367747 q = 1) : d326658 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331330 q = 1) (hb : d367748 q = 1) : d326659 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107528 (p : Pattern) (ha : d331330 p = 1) (hb : d367754 p = 1) : d326665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331330 q = 1) (hb : d367749 q = 1) : d326660 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107527 q ha hb
    | true =>
      simp only [d367749, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331330 q = 1) (hb : d367750 q = 1) : d326661 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331330 q = 1) (hb : d367751 q = 1) : d326662 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331330 q = 1) (hb : d367752 q = 1) : d326663 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331330 q = 1) (hb : d367753 q = 1) : d326664 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331330 q = 1) (hb : d367754 q = 1) : d326665 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107529 (p : Pattern) (ha : d375642 p = 1) (hb : d378989 p = 1) : d379039 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322205 q = 1) : d322205 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322206 q = 1) (hb : d363800 q = 1) : d379037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d322206, d363800, d379037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322206, d363800, d379037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375641 q = 1) (hb : d378989 q = 1) : d379038 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375641, d378989, d379038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375641, d378989, d379038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d378989 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d375642 q = 1) (hb : d378989 q = 1) : d379039 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375642, d379039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375642, d379039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107530 (p : Pattern) (ha : d375648 p = 1) (hb : d378989 p = 1) : d379045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375643 q = 1) (hb : d378989 q = 1) : d379040 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375643, d379040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107529 q ha hb
    | true =>
      simp only [d375643, d379040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375644 q = 1) (hb : d378989 q = 1) : d379041 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375644, d379041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375644, d379041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375645 q = 1) (hb : d378989 q = 1) : d379042 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375645, d379042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375645, d379042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375646 q = 1) (hb : d378989 q = 1) : d379043 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375646, d379043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375646, d379043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375647 q = 1) (hb : d378989 q = 1) : d379044 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375647, d379044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375647, d379044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375648 q = 1) (hb : d378989 q = 1) : d379045 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375648, d379045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375648, d379045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107531 (p : Pattern) (ha : d375654 p = 1) (hb : d378991 p = 1) : d379051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375649 q = 1) (hb : d378989 q = 1) : d379046 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375649, d379046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107530 q ha hb
    | true =>
      simp only [d375649, d379046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375650 q = 1) (hb : d378989 q = 1) : d379047 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375650, d379047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375650, d379047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375651 q = 1) (hb : d378990 q = 1) : d379048 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375651, d378990, d379048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375651, d378990, d379048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d375652 q = 1) (hb : d378991 q = 1) : d379049 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375652, d378991, d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375652, d378991, d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d375653 q = 1) (hb : d378991 q = 1) : d379050 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375653, d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375653, d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375654 q = 1) (hb : d378991 q = 1) : d379051 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375654, d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d375654, d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro107532 (p : Pattern) (ha : d375660 p = 1) (hb : d378991 p = 1) : d379057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375655 q = 1) (hb : d378991 q = 1) : d379052 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375655, d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107531 q ha hb
    | true =>
      simp only [d375655, d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375656 q = 1) (hb : d378991 q = 1) : d379053 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375656, d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375656, d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375657 q = 1) (hb : d378991 q = 1) : d379054 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375657, d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375657, d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375658 q = 1) (hb : d378991 q = 1) : d379055 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375658, d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375658, d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375659 q = 1) (hb : d378991 q = 1) : d379056 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375659, d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375659, d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375660 q = 1) (hb : d378991 q = 1) : d379057 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375660, d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375660, d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107533 (p : Pattern) (ha : d375666 p = 1) (hb : d378991 p = 1) : d379063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375661 q = 1) (hb : d378991 q = 1) : d379058 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375661, d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107532 q ha hb
    | true =>
      simp only [d375661, d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375662 q = 1) (hb : d378991 q = 1) : d379059 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375662, d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375662, d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375663 q = 1) (hb : d378991 q = 1) : d379060 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375663, d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375663, d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375664 q = 1) (hb : d378991 q = 1) : d379061 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375664, d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375664, d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375665 q = 1) (hb : d378991 q = 1) : d379062 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375665, d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375665, d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375666 q = 1) (hb : d378991 q = 1) : d379063 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375666, d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375666, d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107534 (p : Pattern) (ha : d375672 p = 1) (hb : d378991 p = 1) : d379069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375667 q = 1) (hb : d378991 q = 1) : d379064 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375667, d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107533 q ha hb
    | true =>
      simp only [d375667, d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375668 q = 1) (hb : d378991 q = 1) : d379065 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375668, d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375668, d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375669 q = 1) (hb : d378991 q = 1) : d379066 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375669, d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375669, d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375670 q = 1) (hb : d378991 q = 1) : d379067 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375670, d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375670, d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375671 q = 1) (hb : d378991 q = 1) : d379068 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375671, d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375671, d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375672 q = 1) (hb : d378991 q = 1) : d379069 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375672, d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375672, d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107535 (p : Pattern) (ha : d375678 p = 1) (hb : d378991 p = 1) : d379075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375673 q = 1) (hb : d378991 q = 1) : d379070 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375673, d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107534 q ha hb
    | true =>
      simp only [d375673, d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375674 q = 1) (hb : d378991 q = 1) : d379071 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375674, d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375674, d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375675 q = 1) (hb : d378991 q = 1) : d379072 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375675, d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375675, d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375676 q = 1) (hb : d378991 q = 1) : d379073 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375676, d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375676, d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375677 q = 1) (hb : d378991 q = 1) : d379074 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375677, d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375677, d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375678 q = 1) (hb : d378991 q = 1) : d379075 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375678, d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375678, d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107536 (p : Pattern) (ha : d375684 p = 1) (hb : d378991 p = 1) : d379081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375679 q = 1) (hb : d378991 q = 1) : d379076 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375679, d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107535 q ha hb
    | true =>
      simp only [d375679, d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375680 q = 1) (hb : d378991 q = 1) : d379077 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375680, d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375680, d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375681 q = 1) (hb : d378991 q = 1) : d379078 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375681, d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375681, d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375682 q = 1) (hb : d378991 q = 1) : d379079 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375682, d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375682, d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375683 q = 1) (hb : d378991 q = 1) : d379080 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375683, d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375683, d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375684 q = 1) (hb : d378991 q = 1) : d379081 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375684, d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375684, d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107537 (p : Pattern) (ha : d378994 p = 1) (hb : d379039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d322203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105123 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d322205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d378992 q = 1) (hb : d379037 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d378992, d379037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d378992, d379037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d378993 q = 1) (hb : d379038 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d378993, d379038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d378993, d379038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d378994 q = 1) (hb : d379039 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d378994, d379039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d378994, d379039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro107538 (p : Pattern) (ha : d379000 p = 1) (hb : d379045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d378995 q = 1) (hb : d379040 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d378995, d379040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107537 q ha hb
    | true =>
      simp only [d378995, d379040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d378996 q = 1) (hb : d379041 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d378996, d379041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378996, d379041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d378997 q = 1) (hb : d379042 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d378997, d379042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d378997, d379042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d378998 q = 1) (hb : d379043 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d378998, d379043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d378998, d379043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d378999 q = 1) (hb : d379044 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d378999, d379044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d378999, d379044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379000 q = 1) (hb : d379045 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379000, d379045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379000, d379045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107539 (p : Pattern) (ha : d379006 p = 1) (hb : d379051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379001 q = 1) (hb : d379046 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379001, d379046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107538 q ha hb
    | true =>
      simp only [d379001, d379046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379002 q = 1) (hb : d379047 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379002, d379047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379002, d379047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379003 q = 1) (hb : d379048 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379003, d379048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379003, d379048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379004 q = 1) (hb : d379049 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379004, d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379004, d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379005 q = 1) (hb : d379050 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379005, d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379005, d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379006 q = 1) (hb : d379051 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379006, d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379006, d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107540 (p : Pattern) (ha : d379012 p = 1) (hb : d379057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379007 q = 1) (hb : d379052 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379007, d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107539 q ha hb
    | true =>
      simp only [d379007, d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379008 q = 1) (hb : d379053 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379008, d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379008, d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379009 q = 1) (hb : d379054 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379009, d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379009, d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379010 q = 1) (hb : d379055 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379010, d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379010, d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379011 q = 1) (hb : d379056 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379011, d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379011, d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379012 q = 1) (hb : d379057 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379012, d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379012, d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107541 (p : Pattern) (ha : d379018 p = 1) (hb : d379063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379013 q = 1) (hb : d379058 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379013, d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107540 q ha hb
    | true =>
      simp only [d379013, d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379014 q = 1) (hb : d379059 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379014, d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379014, d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379015 q = 1) (hb : d379060 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379015, d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379015, d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379016 q = 1) (hb : d379061 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379016, d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379016, d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379017 q = 1) (hb : d379062 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379017, d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379017, d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379018 q = 1) (hb : d379063 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379018, d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379018, d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107542 (p : Pattern) (ha : d379024 p = 1) (hb : d379069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379019 q = 1) (hb : d379064 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379019, d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107541 q ha hb
    | true =>
      simp only [d379019, d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379020 q = 1) (hb : d379065 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379020, d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379020, d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379021 q = 1) (hb : d379066 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379021, d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379021, d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379022 q = 1) (hb : d379067 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379022, d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379022, d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379023 q = 1) (hb : d379068 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379023, d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379023, d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379024 q = 1) (hb : d379069 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379024, d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379024, d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107543 (p : Pattern) (ha : d379030 p = 1) (hb : d379075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379025 q = 1) (hb : d379070 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379025, d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107542 q ha hb
    | true =>
      simp only [d379025, d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379026 q = 1) (hb : d379071 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379026, d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379026, d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379027 q = 1) (hb : d379072 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379027, d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379027, d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379028 q = 1) (hb : d379073 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379028, d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379028, d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379029 q = 1) (hb : d379074 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379029, d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379029, d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379030 q = 1) (hb : d379075 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379030, d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379030, d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107544 (p : Pattern) (ha : d379036 p = 1) (hb : d379081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379031 q = 1) (hb : d379076 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379031, d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107543 q ha hb
    | true =>
      simp only [d379031, d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379032 q = 1) (hb : d379077 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379032, d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379032, d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379033 q = 1) (hb : d379078 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379033, d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379033, d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379034 q = 1) (hb : d379079 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379034, d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379034, d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379035 q = 1) (hb : d379080 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379035, d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379035, d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379036 q = 1) (hb : d379081 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379036, d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379036, d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107545 (p : Pattern) (ha : d375686 p = 1) (hb : d378989 p = 1) : d379084 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d367709 q = 1) : d367709 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d363800 q = 1) (hb : d367710 q = 1) : d379082 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363800, d367710, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363800, d367710, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375685 q = 1) (hb : d378989 q = 1) : d379083 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375685, d378989, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d375685, d378989, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d378989 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d375686 q = 1) (hb : d378989 q = 1) : d379084 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375686, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375686, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107546 (p : Pattern) (ha : d375692 p = 1) (hb : d378989 p = 1) : d379090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375687 q = 1) (hb : d378989 q = 1) : d379085 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375687, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107545 q ha hb
    | true =>
      simp only [d375687, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375688 q = 1) (hb : d378989 q = 1) : d379086 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375688, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375688, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375689 q = 1) (hb : d378989 q = 1) : d379087 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375689, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375689, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375690 q = 1) (hb : d378989 q = 1) : d379088 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375690, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375690, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375691 q = 1) (hb : d378989 q = 1) : d379089 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375691, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375691, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375692 q = 1) (hb : d378989 q = 1) : d379090 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375692, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375692, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107547 (p : Pattern) (ha : d375698 p = 1) (hb : d378991 p = 1) : d379096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375693 q = 1) (hb : d378989 q = 1) : d379091 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375693, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107546 q ha hb
    | true =>
      simp only [d375693, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375694 q = 1) (hb : d378989 q = 1) : d379092 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375694, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375694, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375695 q = 1) (hb : d378990 q = 1) : d379093 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375695, d378990, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375695, d378990, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d375696 q = 1) (hb : d378991 q = 1) : d379094 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375696, d378991, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375696, d378991, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d375697 q = 1) (hb : d378991 q = 1) : d379095 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375697, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375697, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375698 q = 1) (hb : d378991 q = 1) : d379096 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375698, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d375698, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro107548 (p : Pattern) (ha : d375704 p = 1) (hb : d378991 p = 1) : d379102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375699 q = 1) (hb : d378991 q = 1) : d379097 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375699, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107547 q ha hb
    | true =>
      simp only [d375699, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375700 q = 1) (hb : d378991 q = 1) : d379098 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375700, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375700, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375701 q = 1) (hb : d378991 q = 1) : d379099 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375701, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375701, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375702 q = 1) (hb : d378991 q = 1) : d379100 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375702, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375702, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375703 q = 1) (hb : d378991 q = 1) : d379101 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375703, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375703, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375704 q = 1) (hb : d378991 q = 1) : d379102 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375704, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375704, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107549 (p : Pattern) (ha : d375710 p = 1) (hb : d378991 p = 1) : d379108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375705 q = 1) (hb : d378991 q = 1) : d379103 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375705, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107548 q ha hb
    | true =>
      simp only [d375705, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375706 q = 1) (hb : d378991 q = 1) : d379104 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375706, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375706, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375707 q = 1) (hb : d378991 q = 1) : d379105 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375707, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375707, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375708 q = 1) (hb : d378991 q = 1) : d379106 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375708, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375708, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375709 q = 1) (hb : d378991 q = 1) : d379107 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375709, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375709, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375710 q = 1) (hb : d378991 q = 1) : d379108 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375710, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375710, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107550 (p : Pattern) (ha : d375716 p = 1) (hb : d378991 p = 1) : d379114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375711 q = 1) (hb : d378991 q = 1) : d379109 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375711, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107549 q ha hb
    | true =>
      simp only [d375711, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375712 q = 1) (hb : d378991 q = 1) : d379110 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375712, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375712, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375713 q = 1) (hb : d378991 q = 1) : d379111 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375713, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375713, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375714 q = 1) (hb : d378991 q = 1) : d379112 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375714, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375714, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375715 q = 1) (hb : d378991 q = 1) : d379113 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375715, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375715, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375716 q = 1) (hb : d378991 q = 1) : d379114 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375716, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375716, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107551 (p : Pattern) (ha : d375722 p = 1) (hb : d378991 p = 1) : d379120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375717 q = 1) (hb : d378991 q = 1) : d379115 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375717, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107550 q ha hb
    | true =>
      simp only [d375717, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375718 q = 1) (hb : d378991 q = 1) : d379116 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375718, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375718, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375719 q = 1) (hb : d378991 q = 1) : d379117 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375719, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375719, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375720 q = 1) (hb : d378991 q = 1) : d379118 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375720, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375720, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375721 q = 1) (hb : d378991 q = 1) : d379119 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375721, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375721, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375722 q = 1) (hb : d378991 q = 1) : d379120 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375722, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375722, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107552 (p : Pattern) (ha : d375728 p = 1) (hb : d378991 p = 1) : d379126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d378991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375723 q = 1) (hb : d378991 q = 1) : d379121 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375723, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107551 q ha hb
    | true =>
      simp only [d375723, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375724 q = 1) (hb : d378991 q = 1) : d379122 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375724, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375724, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375725 q = 1) (hb : d378991 q = 1) : d379123 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375725, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375725, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375726 q = 1) (hb : d378991 q = 1) : d379124 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375726, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375726, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375727 q = 1) (hb : d378991 q = 1) : d379125 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375727, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375727, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375728 q = 1) (hb : d378991 q = 1) : d379126 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375728, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375728, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107553 (p : Pattern) (ha : d378994 p = 1) (hb : d379084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105156 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d378992 q = 1) (hb : d379082 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d378992, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d378992, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d378993 q = 1) (hb : d379083 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d378993, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d378993, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d378994 q = 1) (hb : d379084 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d378994, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d378994, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro107554 (p : Pattern) (ha : d379000 p = 1) (hb : d379090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d378995 q = 1) (hb : d379085 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d378995, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107553 q ha hb
    | true =>
      simp only [d378995, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d378996 q = 1) (hb : d379086 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d378996, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378996, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d378997 q = 1) (hb : d379087 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d378997, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d378997, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d378998 q = 1) (hb : d379088 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d378998, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d378998, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d378999 q = 1) (hb : d379089 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d378999, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d378999, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379000 q = 1) (hb : d379090 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379000, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379000, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107555 (p : Pattern) (ha : d379006 p = 1) (hb : d379096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379001 q = 1) (hb : d379091 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379001, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107554 q ha hb
    | true =>
      simp only [d379001, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379002 q = 1) (hb : d379092 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379002, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379002, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379003 q = 1) (hb : d379093 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379003, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379003, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379004 q = 1) (hb : d379094 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379004, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379004, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379005 q = 1) (hb : d379095 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379005, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379005, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379006 q = 1) (hb : d379096 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379006, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379006, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107556 (p : Pattern) (ha : d379012 p = 1) (hb : d379102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379007 q = 1) (hb : d379097 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379007, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107555 q ha hb
    | true =>
      simp only [d379007, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379008 q = 1) (hb : d379098 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379008, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379008, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379009 q = 1) (hb : d379099 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379009, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379009, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379010 q = 1) (hb : d379100 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379010, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379010, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379011 q = 1) (hb : d379101 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379011, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379011, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379012 q = 1) (hb : d379102 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379012, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379012, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107557 (p : Pattern) (ha : d379018 p = 1) (hb : d379108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379013 q = 1) (hb : d379103 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379013, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107556 q ha hb
    | true =>
      simp only [d379013, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379014 q = 1) (hb : d379104 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379014, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379014, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379015 q = 1) (hb : d379105 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379015, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379015, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379016 q = 1) (hb : d379106 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379016, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379016, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379017 q = 1) (hb : d379107 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379017, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379017, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379018 q = 1) (hb : d379108 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379018, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379018, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107558 (p : Pattern) (ha : d379024 p = 1) (hb : d379114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379019 q = 1) (hb : d379109 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379019, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107557 q ha hb
    | true =>
      simp only [d379019, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379020 q = 1) (hb : d379110 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379020, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379020, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379021 q = 1) (hb : d379111 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379021, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379021, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379022 q = 1) (hb : d379112 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379022, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379022, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379023 q = 1) (hb : d379113 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379023, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379023, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379024 q = 1) (hb : d379114 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379024, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379024, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107559 (p : Pattern) (ha : d379030 p = 1) (hb : d379120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379025 q = 1) (hb : d379115 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379025, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107558 q ha hb
    | true =>
      simp only [d379025, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379026 q = 1) (hb : d379116 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379026, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379026, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379027 q = 1) (hb : d379117 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379027, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379027, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379028 q = 1) (hb : d379118 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379028, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379028, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379029 q = 1) (hb : d379119 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379029, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379029, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379030 q = 1) (hb : d379120 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379030, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379030, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107560 (p : Pattern) (ha : d379036 p = 1) (hb : d379126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379031 q = 1) (hb : d379121 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379031, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107559 q ha hb
    | true =>
      simp only [d379031, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379032 q = 1) (hb : d379122 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379032, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379032, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379033 q = 1) (hb : d379123 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379033, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379033, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379034 q = 1) (hb : d379124 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379034, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379034, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379035 q = 1) (hb : d379125 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379035, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379035, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379036 q = 1) (hb : d379126 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379036, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379036, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107561 (p : Pattern) (ha : d379039 p = 1) (hb : d379084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322203 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105188 q ha hb
  have h5 (q : Pattern) (ha : d322204 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322205 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379037 q = 1) (hb : d379082 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379037, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379037, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d379038 q = 1) (hb : d379083 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379038, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379038, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d379039 q = 1) (hb : d379084 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379039, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379039, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h9 p ha hb
theorem andIntro107562 (p : Pattern) (ha : d379045 p = 1) (hb : d379090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379040 q = 1) (hb : d379085 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379040, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107561 q ha hb
    | true =>
      simp only [d379040, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379041 q = 1) (hb : d379086 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379041, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379041, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379042 q = 1) (hb : d379087 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379042, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379042, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379043 q = 1) (hb : d379088 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379043, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379043, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379044 q = 1) (hb : d379089 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379044, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379044, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379045 q = 1) (hb : d379090 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379045, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379045, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107563 (p : Pattern) (ha : d379051 p = 1) (hb : d379096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379046 q = 1) (hb : d379091 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379046, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107562 q ha hb
    | true =>
      simp only [d379046, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379047 q = 1) (hb : d379092 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379047, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379047, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379048 q = 1) (hb : d379093 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379048, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379048, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379049 q = 1) (hb : d379094 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379049, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379049, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379050 q = 1) (hb : d379095 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379050, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379050, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379051 q = 1) (hb : d379096 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379051, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379051, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107564 (p : Pattern) (ha : d379057 p = 1) (hb : d379102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379052 q = 1) (hb : d379097 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379052, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107563 q ha hb
    | true =>
      simp only [d379052, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379053 q = 1) (hb : d379098 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379053, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379053, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379054 q = 1) (hb : d379099 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379054, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379054, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379055 q = 1) (hb : d379100 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379055, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379055, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379056 q = 1) (hb : d379101 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379056, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379056, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379057 q = 1) (hb : d379102 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379057, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379057, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107565 (p : Pattern) (ha : d379063 p = 1) (hb : d379108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379058 q = 1) (hb : d379103 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379058, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107564 q ha hb
    | true =>
      simp only [d379058, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379059 q = 1) (hb : d379104 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379059, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379059, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379060 q = 1) (hb : d379105 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379060, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379060, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379061 q = 1) (hb : d379106 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379061, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379061, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379062 q = 1) (hb : d379107 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379062, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379062, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379063 q = 1) (hb : d379108 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379063, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379063, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107566 (p : Pattern) (ha : d379069 p = 1) (hb : d379114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379064 q = 1) (hb : d379109 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379064, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107565 q ha hb
    | true =>
      simp only [d379064, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379065 q = 1) (hb : d379110 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379065, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379065, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379066 q = 1) (hb : d379111 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379066, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379066, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379067 q = 1) (hb : d379112 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379067, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379067, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379068 q = 1) (hb : d379113 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379068, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379068, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379069 q = 1) (hb : d379114 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379069, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379069, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107567 (p : Pattern) (ha : d379075 p = 1) (hb : d379120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379070 q = 1) (hb : d379115 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379070, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107566 q ha hb
    | true =>
      simp only [d379070, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379071 q = 1) (hb : d379116 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379071, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379071, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379072 q = 1) (hb : d379117 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379072, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379072, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379073 q = 1) (hb : d379118 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379073, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379073, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379074 q = 1) (hb : d379119 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379074, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379074, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379075 q = 1) (hb : d379120 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379075, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379075, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107568 (p : Pattern) (ha : d379081 p = 1) (hb : d379126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379076 q = 1) (hb : d379121 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379076, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107567 q ha hb
    | true =>
      simp only [d379076, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379077 q = 1) (hb : d379122 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379077, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379077, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379078 q = 1) (hb : d379123 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379078, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379078, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379079 q = 1) (hb : d379124 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379079, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379079, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379080 q = 1) (hb : d379125 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379080, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379080, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379081 q = 1) (hb : d379126 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379081, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379081, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107569 (p : Pattern) (ha : d375654 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d375651 q = 1) (hb : d379134 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375651, d379134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d375651, d379134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375652 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375652, d379135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375652, d379135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d375653 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375654 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107570 (p : Pattern) (ha : d375660 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375655 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107569 q ha hb
    | true =>
      simp only [d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375656 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375657 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375658 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375659 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375660 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107571 (p : Pattern) (ha : d375666 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375661 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107570 q ha hb
    | true =>
      simp only [d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375662 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375663 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375664 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375665 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375666 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107572 (p : Pattern) (ha : d375672 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375667 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107571 q ha hb
    | true =>
      simp only [d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375668 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375669 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375670 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375671 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375672 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107573 (p : Pattern) (ha : d375678 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375673 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107572 q ha hb
    | true =>
      simp only [d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375674 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375675 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375676 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375677 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375678 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107574 (p : Pattern) (ha : d375684 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375679 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107573 q ha hb
    | true =>
      simp only [d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375680 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375681 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375682 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375683 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375684 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107575 (p : Pattern) (ha : d0 p = 1) (hb : d379223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379223 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107576 (p : Pattern) (ha : d375698 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375694 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d375695 q = 1) (hb : d379134 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375695, d379134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d375695, d379134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375696 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375696, d379135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375696, d379135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d375697 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375698 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107577 (p : Pattern) (ha : d375704 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375699 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107576 q ha hb
    | true =>
      simp only [d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375700 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375701 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375702 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375703 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375704 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107578 (p : Pattern) (ha : d375710 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375705 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107577 q ha hb
    | true =>
      simp only [d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375706 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375707 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375708 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375709 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375710 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107579 (p : Pattern) (ha : d375716 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375711 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107578 q ha hb
    | true =>
      simp only [d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375712 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375713 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375714 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375715 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375716 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107580 (p : Pattern) (ha : d375722 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375717 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107579 q ha hb
    | true =>
      simp only [d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375718 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375719 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375720 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375721 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375722 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107581 (p : Pattern) (ha : d375728 p = 1) (hb : d379135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375723 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107580 q ha hb
    | true =>
      simp only [d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375724 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375725 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375726 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375727 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375728 q = 1) (hb : d379135 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107582 (p : Pattern) (ha : d0 p = 1) (hb : d379267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379267 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107583 (p : Pattern) (ha : d375654 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d375651 q = 1) (hb : d379270 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375651, d379270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d375651, d379270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375652 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375652, d379271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375652, d379271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d375653 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375654 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107584 (p : Pattern) (ha : d375660 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375655 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107583 q ha hb
    | true =>
      simp only [d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375656 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375657 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375658 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375659 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375660 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107585 (p : Pattern) (ha : d375666 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375661 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107584 q ha hb
    | true =>
      simp only [d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375662 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375663 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375664 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375665 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375666 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107586 (p : Pattern) (ha : d375672 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375667 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107585 q ha hb
    | true =>
      simp only [d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375668 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375669 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375670 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375671 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375672 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107587 (p : Pattern) (ha : d375678 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375673 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107586 q ha hb
    | true =>
      simp only [d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375674 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375675 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375676 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375677 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375678 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107588 (p : Pattern) (ha : d375684 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375679 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107587 q ha hb
    | true =>
      simp only [d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375680 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375681 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375682 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375683 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375684 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107589 (p : Pattern) (ha : d375698 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375694 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d375695 q = 1) (hb : d379270 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375695, d379270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d375695, d379270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d375696 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375696, d379271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375696, d379271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d375697 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375698 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107590 (p : Pattern) (ha : d375704 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375699 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107589 q ha hb
    | true =>
      simp only [d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375700 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375701 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375702 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375703 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375704 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107591 (p : Pattern) (ha : d375710 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375705 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107590 q ha hb
    | true =>
      simp only [d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375706 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375707 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375708 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375709 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375710 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107592 (p : Pattern) (ha : d375716 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375711 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107591 q ha hb
    | true =>
      simp only [d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375712 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375713 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375714 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375715 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375716 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107593 (p : Pattern) (ha : d375722 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375717 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107592 q ha hb
    | true =>
      simp only [d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375718 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375719 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375720 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375721 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375722 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107594 (p : Pattern) (ha : d375728 p = 1) (hb : d379271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375723 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107593 q ha hb
    | true =>
      simp only [d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375724 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375725 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375726 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375727 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375728 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107595 (p : Pattern) (ha : d375596 p = 1) (hb : d375684 p = 1) : d375684 p = 1 := by
  have h0 (q : Pattern) (ha : d375596 q = 1) (hb : d375684 q = 1) : d375684 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107596 (p : Pattern) (ha : d320471 p = 1) (hb : d375642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d322203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105123 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d322205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86233 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d322206 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d320469 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d320470 q = 1) (hb : d375641 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d375641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d375641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d320471 q = 1) (hb : d375642 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d375642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320471, d375642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro107597 (p : Pattern) (ha : d320477 p = 1) (hb : d375648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d375643 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d375643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107596 q ha hb
    | true =>
      simp only [d320472, d375643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d375644 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d375644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d375644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d375645 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d375645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d375645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d375646 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d375646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d375646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d375647 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d375647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d375647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d375648 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d375648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d375648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107598 (p : Pattern) (ha : d320483 p = 1) (hb : d375654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d375649 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d375649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107597 q ha hb
    | true =>
      simp only [d320478, d375649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d375650 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d375650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d375650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d375651 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d375651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d375651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d375652 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d375652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d375652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d375653 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d375654 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107599 (p : Pattern) (ha : d320489 p = 1) (hb : d375660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d375655 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107598 q ha hb
    | true =>
      simp only [d320484, d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d375656 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d375657 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d375658 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d375659 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d375660 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107600 (p : Pattern) (ha : d320495 p = 1) (hb : d375666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d375661 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107599 q ha hb
    | true =>
      simp only [d320490, d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d375662 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d375663 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d375664 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d375665 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d375666 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107601 (p : Pattern) (ha : d320501 p = 1) (hb : d375672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d375667 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107600 q ha hb
    | true =>
      simp only [d320496, d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d375668 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d375669 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d375670 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d375671 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d375672 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107602 (p : Pattern) (ha : d320507 p = 1) (hb : d375678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d375673 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107601 q ha hb
    | true =>
      simp only [d320502, d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d375674 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d375675 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d375676 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d375677 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d375678 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107603 (p : Pattern) (ha : d320513 p = 1) (hb : d375684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d375679 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107602 q ha hb
    | true =>
      simp only [d320508, d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d375680 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d375681 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d375682 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d375683 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d375684 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107604 (p : Pattern) (ha : d375596 p = 1) (hb : d375728 p = 1) : d375728 p = 1 := by
  have h0 (q : Pattern) (ha : d375596 q = 1) (hb : d375728 q = 1) : d375728 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107605 (p : Pattern) (ha : d320471 p = 1) (hb : d375686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105156 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86365 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d320469 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d320470 q = 1) (hb : d375685 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d320471 q = 1) (hb : d375686 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320471, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro107606 (p : Pattern) (ha : d320477 p = 1) (hb : d375692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d375687 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107605 q ha hb
    | true =>
      simp only [d320472, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d375688 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d375689 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d375690 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d375691 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d375692 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107607 (p : Pattern) (ha : d320483 p = 1) (hb : d375698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d375693 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107606 q ha hb
    | true =>
      simp only [d320478, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d375694 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d375695 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d375696 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d375697 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d375698 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107608 (p : Pattern) (ha : d320489 p = 1) (hb : d375704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d375699 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107607 q ha hb
    | true =>
      simp only [d320484, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d375700 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d375701 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d375702 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d375703 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d375704 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107609 (p : Pattern) (ha : d320495 p = 1) (hb : d375710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d375705 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107608 q ha hb
    | true =>
      simp only [d320490, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d375706 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d375707 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d375708 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d375709 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d375710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107610 (p : Pattern) (ha : d320501 p = 1) (hb : d375716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d375711 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107609 q ha hb
    | true =>
      simp only [d320496, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d375712 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d375713 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d375714 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d375715 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d375716 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107611 (p : Pattern) (ha : d320507 p = 1) (hb : d375722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d375717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107610 q ha hb
    | true =>
      simp only [d320502, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d375718 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d375719 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d375720 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d375721 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d375722 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107612 (p : Pattern) (ha : d320513 p = 1) (hb : d375728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d375723 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107611 q ha hb
    | true =>
      simp only [d320508, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d375724 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d375725 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d375726 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d375727 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d375728 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107613 (p : Pattern) (ha : d322208 p = 1) (hb : d375686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322203 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105188 q ha hb
  have h5 (q : Pattern) (ha : d322204 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322205 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321678 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86389 q ha hb
  have h8 (q : Pattern) (ha : d321679 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321680 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322206 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d322206, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322206, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d322207 q = 1) (hb : d375685 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d322207, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322207, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d322208 q = 1) (hb : d375686 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d322208, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322208, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h13 p ha hb
theorem andIntro107614 (p : Pattern) (ha : d322214 p = 1) (hb : d375692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322209 q = 1) (hb : d375687 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d322209, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107613 q ha hb
    | true =>
      simp only [d322209, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322210 q = 1) (hb : d375688 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d322210, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322210, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322211 q = 1) (hb : d375689 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d322211, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322211, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322212 q = 1) (hb : d375690 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d322212, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322212, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322213 q = 1) (hb : d375691 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d322213, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322213, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322214 q = 1) (hb : d375692 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d322214, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322214, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107615 (p : Pattern) (ha : d322220 p = 1) (hb : d375698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322215 q = 1) (hb : d375693 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d322215, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107614 q ha hb
    | true =>
      simp only [d322215, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322216 q = 1) (hb : d375694 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d322216, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322216, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322217 q = 1) (hb : d375695 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d322217, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322217, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322218 q = 1) (hb : d375696 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322218, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322219 q = 1) (hb : d375697 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322219, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322220 q = 1) (hb : d375698 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322220, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107616 (p : Pattern) (ha : d322226 p = 1) (hb : d375704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d375699 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107615 q ha hb
    | true =>
      simp only [d322221, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d375700 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d375701 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d375702 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d375703 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d375704 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107617 (p : Pattern) (ha : d322232 p = 1) (hb : d375710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d375705 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107616 q ha hb
    | true =>
      simp only [d322227, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d375706 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d375707 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d375708 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d375709 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d375710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107618 (p : Pattern) (ha : d322238 p = 1) (hb : d375716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d375711 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107617 q ha hb
    | true =>
      simp only [d322233, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d375712 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d375713 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d375714 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d375715 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d375716 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107619 (p : Pattern) (ha : d322244 p = 1) (hb : d375722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d375717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107618 q ha hb
    | true =>
      simp only [d322239, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d375718 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d375719 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d375720 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d375721 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d375722 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107620 (p : Pattern) (ha : d322250 p = 1) (hb : d375728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d375723 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107619 q ha hb
    | true =>
      simp only [d322245, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d375724 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d375725 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d375726 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d375727 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d375728 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107621 (p : Pattern) (ha : d370936 p = 1) (hb : d375654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d370935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375653 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d370936, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370936, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375654 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro107622 (p : Pattern) (ha : d370936 p = 1) (hb : d375660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375655 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107621 q ha hb
    | true =>
      simp only [d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375656 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375657 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375658 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375659 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375660 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107623 (p : Pattern) (ha : d370936 p = 1) (hb : d375666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375661 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107622 q ha hb
    | true =>
      simp only [d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375662 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375663 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375664 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375665 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375666 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107624 (p : Pattern) (ha : d370936 p = 1) (hb : d375672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375667 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107623 q ha hb
    | true =>
      simp only [d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375668 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375669 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375670 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375671 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375672 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107625 (p : Pattern) (ha : d370936 p = 1) (hb : d375678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375673 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107624 q ha hb
    | true =>
      simp only [d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375674 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375675 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375676 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375677 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375678 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107626 (p : Pattern) (ha : d370936 p = 1) (hb : d375684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375679 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107625 q ha hb
    | true =>
      simp only [d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375680 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375681 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375682 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375683 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375684 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107627 (p : Pattern) (ha : d370936 p = 1) (hb : d375698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375696 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d370935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375697 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d370936, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370936, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375698 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro107628 (p : Pattern) (ha : d370936 p = 1) (hb : d375704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375699 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107627 q ha hb
    | true =>
      simp only [d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375700 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375701 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375702 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375703 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375704 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107629 (p : Pattern) (ha : d370936 p = 1) (hb : d375710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375705 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107628 q ha hb
    | true =>
      simp only [d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375706 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375707 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375708 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375709 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107630 (p : Pattern) (ha : d370936 p = 1) (hb : d375716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375711 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107629 q ha hb
    | true =>
      simp only [d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375712 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375713 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375714 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375715 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375716 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107631 (p : Pattern) (ha : d370936 p = 1) (hb : d375722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107630 q ha hb
    | true =>
      simp only [d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375718 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375719 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375720 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375721 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375722 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107632 (p : Pattern) (ha : d370936 p = 1) (hb : d375728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370936 q = 1) (hb : d375723 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107631 q ha hb
    | true =>
      simp only [d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d370936 q = 1) (hb : d375724 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d370936 q = 1) (hb : d375725 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370936 q = 1) (hb : d375726 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d370936 q = 1) (hb : d375727 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d370936 q = 1) (hb : d375728 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107633 (p : Pattern) (ha : d379039 p = 1) (hb : d379275 p = 1) : d379327 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322163 q = 1) : d322163 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322205 q = 1) (hb : d364397 q = 1) : d379324 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d364397, d379324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322205, d364397, d379324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379037 q = 1) (hb : d379275 q = 1) : d379325 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379037, d379275, d379325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379037, d379275, d379325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379275 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379038 q = 1) (hb : d379275 q = 1) : d379326 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379038, d379326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379038, d379326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379039 q = 1) (hb : d379275 q = 1) : d379327 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379039, d379327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379039, d379327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107634 (p : Pattern) (ha : d379045 p = 1) (hb : d379275 p = 1) : d379333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379040 q = 1) (hb : d379275 q = 1) : d379328 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379040, d379328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107633 q ha hb
    | true =>
      simp only [d379040, d379328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379041 q = 1) (hb : d379275 q = 1) : d379329 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379041, d379329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379041, d379329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379042 q = 1) (hb : d379275 q = 1) : d379330 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379042, d379330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379042, d379330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379043 q = 1) (hb : d379275 q = 1) : d379331 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379043, d379331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379043, d379331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379044 q = 1) (hb : d379275 q = 1) : d379332 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379044, d379332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379044, d379332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379045 q = 1) (hb : d379275 q = 1) : d379333 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379045, d379333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379045, d379333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107635 (p : Pattern) (ha : d379051 p = 1) (hb : d379277 p = 1) : d379339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379046 q = 1) (hb : d379275 q = 1) : d379334 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379046, d379334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107634 q ha hb
    | true =>
      simp only [d379046, d379334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379047 q = 1) (hb : d379276 q = 1) : d379335 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379047, d379276, d379335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379047, d379276, d379335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379048 q = 1) (hb : d379277 q = 1) : d379336 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379048, d379277, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379048, d379277, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379049 q = 1) (hb : d379277 q = 1) : d379337 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379049, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379049, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379050 q = 1) (hb : d379277 q = 1) : d379338 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379050, d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379050, d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379051 q = 1) (hb : d379277 q = 1) : d379339 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379051, d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379051, d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107636 (p : Pattern) (ha : d379057 p = 1) (hb : d379277 p = 1) : d379345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379052 q = 1) (hb : d379277 q = 1) : d379340 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379052, d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107635 q ha hb
    | true =>
      simp only [d379052, d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379053 q = 1) (hb : d379277 q = 1) : d379341 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379053, d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379053, d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379054 q = 1) (hb : d379277 q = 1) : d379342 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379054, d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379054, d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379055 q = 1) (hb : d379277 q = 1) : d379343 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379055, d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379055, d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379056 q = 1) (hb : d379277 q = 1) : d379344 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379056, d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379056, d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379057 q = 1) (hb : d379277 q = 1) : d379345 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379057, d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379057, d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107637 (p : Pattern) (ha : d379063 p = 1) (hb : d379277 p = 1) : d379351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379058 q = 1) (hb : d379277 q = 1) : d379346 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379058, d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107636 q ha hb
    | true =>
      simp only [d379058, d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379059 q = 1) (hb : d379277 q = 1) : d379347 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379059, d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379059, d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379060 q = 1) (hb : d379277 q = 1) : d379348 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379060, d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379060, d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379061 q = 1) (hb : d379277 q = 1) : d379349 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379061, d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379061, d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379062 q = 1) (hb : d379277 q = 1) : d379350 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379062, d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379062, d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379063 q = 1) (hb : d379277 q = 1) : d379351 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379063, d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379063, d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107638 (p : Pattern) (ha : d379069 p = 1) (hb : d379277 p = 1) : d379357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379064 q = 1) (hb : d379277 q = 1) : d379352 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379064, d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107637 q ha hb
    | true =>
      simp only [d379064, d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379065 q = 1) (hb : d379277 q = 1) : d379353 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379065, d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379065, d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379066 q = 1) (hb : d379277 q = 1) : d379354 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379066, d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379066, d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379067 q = 1) (hb : d379277 q = 1) : d379355 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379067, d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379067, d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379068 q = 1) (hb : d379277 q = 1) : d379356 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379068, d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379068, d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379069 q = 1) (hb : d379277 q = 1) : d379357 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379069, d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379069, d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107639 (p : Pattern) (ha : d379075 p = 1) (hb : d379277 p = 1) : d379363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379070 q = 1) (hb : d379277 q = 1) : d379358 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379070, d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107638 q ha hb
    | true =>
      simp only [d379070, d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379071 q = 1) (hb : d379277 q = 1) : d379359 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379071, d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379071, d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379072 q = 1) (hb : d379277 q = 1) : d379360 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379072, d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379072, d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379073 q = 1) (hb : d379277 q = 1) : d379361 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379073, d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379073, d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379074 q = 1) (hb : d379277 q = 1) : d379362 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379074, d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379074, d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379075 q = 1) (hb : d379277 q = 1) : d379363 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379075, d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379075, d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107640 (p : Pattern) (ha : d379081 p = 1) (hb : d379277 p = 1) : d379369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379076 q = 1) (hb : d379277 q = 1) : d379364 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379076, d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107639 q ha hb
    | true =>
      simp only [d379076, d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379077 q = 1) (hb : d379277 q = 1) : d379365 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379077, d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379077, d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379078 q = 1) (hb : d379277 q = 1) : d379366 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379078, d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379078, d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379079 q = 1) (hb : d379277 q = 1) : d379367 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379079, d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379079, d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379080 q = 1) (hb : d379277 q = 1) : d379368 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379080, d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379080, d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379081 q = 1) (hb : d379277 q = 1) : d379369 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379081, d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379081, d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107641 (p : Pattern) (ha : d379281 p = 1) (hb : d379327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379278 q = 1) (hb : d379324 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379278, d379324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379278, d379324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d379279 q = 1) (hb : d379325 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379279, d379325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379279, d379325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d379280 q = 1) (hb : d379326 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379280, d379326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379280, d379326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d379281 q = 1) (hb : d379327 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379281, d379327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379281, d379327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro107642 (p : Pattern) (ha : d379287 p = 1) (hb : d379333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379282 q = 1) (hb : d379328 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379282, d379328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107641 q ha hb
    | true =>
      simp only [d379282, d379328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379283 q = 1) (hb : d379329 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379283, d379329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379283, d379329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379284 q = 1) (hb : d379330 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379284, d379330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379284, d379330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379285 q = 1) (hb : d379331 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379285, d379331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379285, d379331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379286 q = 1) (hb : d379332 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379286, d379332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379286, d379332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379287 q = 1) (hb : d379333 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379287, d379333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379287, d379333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107643 (p : Pattern) (ha : d379293 p = 1) (hb : d379339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379288 q = 1) (hb : d379334 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379288, d379334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107642 q ha hb
    | true =>
      simp only [d379288, d379334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379289 q = 1) (hb : d379335 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379289, d379335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379289, d379335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379290 q = 1) (hb : d379336 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379290, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379290, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379291 q = 1) (hb : d379337 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379291, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379291, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379292 q = 1) (hb : d379338 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379292, d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379292, d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379293 q = 1) (hb : d379339 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379293, d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379293, d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107644 (p : Pattern) (ha : d379299 p = 1) (hb : d379345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379294 q = 1) (hb : d379340 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379294, d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107643 q ha hb
    | true =>
      simp only [d379294, d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379295 q = 1) (hb : d379341 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379295, d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379295, d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379296 q = 1) (hb : d379342 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379296, d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379296, d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379297 q = 1) (hb : d379343 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379297, d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379297, d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379298 q = 1) (hb : d379344 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379298, d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379298, d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379299 q = 1) (hb : d379345 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379299, d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379299, d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107645 (p : Pattern) (ha : d379305 p = 1) (hb : d379351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379300 q = 1) (hb : d379346 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379300, d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107644 q ha hb
    | true =>
      simp only [d379300, d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379301 q = 1) (hb : d379347 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379301, d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379301, d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379302 q = 1) (hb : d379348 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379302, d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379302, d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379303 q = 1) (hb : d379349 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379303, d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379303, d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379304 q = 1) (hb : d379350 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379304, d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379304, d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379305 q = 1) (hb : d379351 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379305, d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379305, d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107646 (p : Pattern) (ha : d379311 p = 1) (hb : d379357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379306 q = 1) (hb : d379352 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379306, d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107645 q ha hb
    | true =>
      simp only [d379306, d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379307 q = 1) (hb : d379353 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379307, d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379307, d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379308 q = 1) (hb : d379354 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379308, d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379308, d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379309 q = 1) (hb : d379355 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379309, d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379309, d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379310 q = 1) (hb : d379356 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379310, d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379310, d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379311 q = 1) (hb : d379357 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379311, d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379311, d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107647 (p : Pattern) (ha : d379317 p = 1) (hb : d379363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379312 q = 1) (hb : d379358 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379312, d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107646 q ha hb
    | true =>
      simp only [d379312, d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379313 q = 1) (hb : d379359 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379313, d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379313, d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379314 q = 1) (hb : d379360 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379314, d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379314, d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379315 q = 1) (hb : d379361 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379315, d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379315, d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379316 q = 1) (hb : d379362 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379316, d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379316, d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379317 q = 1) (hb : d379363 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379317, d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379317, d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107648 (p : Pattern) (ha : d379323 p = 1) (hb : d379369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379318 q = 1) (hb : d379364 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379318, d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107647 q ha hb
    | true =>
      simp only [d379318, d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379319 q = 1) (hb : d379365 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379319, d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379319, d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379320 q = 1) (hb : d379366 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379320, d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379320, d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379321 q = 1) (hb : d379367 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379321, d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379321, d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379322 q = 1) (hb : d379368 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379322, d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379322, d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379323 q = 1) (hb : d379369 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379323, d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379323, d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107649 (p : Pattern) (ha : d379084 p = 1) (hb : d379275 p = 1) : d379373 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d367680 q = 1) : d367680 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d364397 q = 1) (hb : d367709 q = 1) : d379370 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364397, d367709, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d364397, d367709, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379082 q = 1) (hb : d379275 q = 1) : d379371 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379082, d379275, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d379082, d379275, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379275 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379083 q = 1) (hb : d379275 q = 1) : d379372 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379083, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379083, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379084 q = 1) (hb : d379275 q = 1) : d379373 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379084, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379084, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107650 (p : Pattern) (ha : d379090 p = 1) (hb : d379275 p = 1) : d379379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379085 q = 1) (hb : d379275 q = 1) : d379374 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379085, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107649 q ha hb
    | true =>
      simp only [d379085, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379086 q = 1) (hb : d379275 q = 1) : d379375 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379086, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379086, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379087 q = 1) (hb : d379275 q = 1) : d379376 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379087, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379087, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379088 q = 1) (hb : d379275 q = 1) : d379377 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379088, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379088, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379089 q = 1) (hb : d379275 q = 1) : d379378 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379089, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379089, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379090 q = 1) (hb : d379275 q = 1) : d379379 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379090, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379090, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107651 (p : Pattern) (ha : d379096 p = 1) (hb : d379277 p = 1) : d379385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379091 q = 1) (hb : d379275 q = 1) : d379380 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379091, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107650 q ha hb
    | true =>
      simp only [d379091, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379092 q = 1) (hb : d379276 q = 1) : d379381 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379092, d379276, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379092, d379276, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379093 q = 1) (hb : d379277 q = 1) : d379382 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379093, d379277, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379093, d379277, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379094 q = 1) (hb : d379277 q = 1) : d379383 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379094, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379094, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379095 q = 1) (hb : d379277 q = 1) : d379384 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379095, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379095, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379096 q = 1) (hb : d379277 q = 1) : d379385 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379096, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379096, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107652 (p : Pattern) (ha : d379102 p = 1) (hb : d379277 p = 1) : d379391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379097 q = 1) (hb : d379277 q = 1) : d379386 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379097, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107651 q ha hb
    | true =>
      simp only [d379097, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379098 q = 1) (hb : d379277 q = 1) : d379387 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379098, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379098, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379099 q = 1) (hb : d379277 q = 1) : d379388 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379099, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379099, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379100 q = 1) (hb : d379277 q = 1) : d379389 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379100, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379100, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379101 q = 1) (hb : d379277 q = 1) : d379390 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379101, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379101, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379102 q = 1) (hb : d379277 q = 1) : d379391 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379102, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379102, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107653 (p : Pattern) (ha : d379108 p = 1) (hb : d379277 p = 1) : d379397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379103 q = 1) (hb : d379277 q = 1) : d379392 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379103, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107652 q ha hb
    | true =>
      simp only [d379103, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379104 q = 1) (hb : d379277 q = 1) : d379393 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379104, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379104, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379105 q = 1) (hb : d379277 q = 1) : d379394 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379105, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379105, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379106 q = 1) (hb : d379277 q = 1) : d379395 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379106, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379106, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379107 q = 1) (hb : d379277 q = 1) : d379396 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379107, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379107, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379108 q = 1) (hb : d379277 q = 1) : d379397 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379108, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379108, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107654 (p : Pattern) (ha : d379114 p = 1) (hb : d379277 p = 1) : d379403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379109 q = 1) (hb : d379277 q = 1) : d379398 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379109, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107653 q ha hb
    | true =>
      simp only [d379109, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379110 q = 1) (hb : d379277 q = 1) : d379399 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379110, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379110, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379111 q = 1) (hb : d379277 q = 1) : d379400 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379111, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379111, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379112 q = 1) (hb : d379277 q = 1) : d379401 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379112, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379112, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379113 q = 1) (hb : d379277 q = 1) : d379402 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379113, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379113, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379114 q = 1) (hb : d379277 q = 1) : d379403 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379114, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379114, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107655 (p : Pattern) (ha : d379120 p = 1) (hb : d379277 p = 1) : d379409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379115 q = 1) (hb : d379277 q = 1) : d379404 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379115, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107654 q ha hb
    | true =>
      simp only [d379115, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379116 q = 1) (hb : d379277 q = 1) : d379405 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379116, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379116, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379117 q = 1) (hb : d379277 q = 1) : d379406 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379117, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379117, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379118 q = 1) (hb : d379277 q = 1) : d379407 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379118, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379118, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379119 q = 1) (hb : d379277 q = 1) : d379408 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379119, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379119, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379120 q = 1) (hb : d379277 q = 1) : d379409 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379120, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379120, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107656 (p : Pattern) (ha : d379126 p = 1) (hb : d379277 p = 1) : d379415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379121 q = 1) (hb : d379277 q = 1) : d379410 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379121, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107655 q ha hb
    | true =>
      simp only [d379121, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379122 q = 1) (hb : d379277 q = 1) : d379411 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379122, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379122, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379123 q = 1) (hb : d379277 q = 1) : d379412 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379123, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379123, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379124 q = 1) (hb : d379277 q = 1) : d379413 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379124, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379124, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379125 q = 1) (hb : d379277 q = 1) : d379414 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379125, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379125, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379126 q = 1) (hb : d379277 q = 1) : d379415 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379126, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379126, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107657 (p : Pattern) (ha : d379281 p = 1) (hb : d379373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379278 q = 1) (hb : d379370 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379278, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379278, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d379279 q = 1) (hb : d379371 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379279, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379279, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d379280 q = 1) (hb : d379372 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379280, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379280, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d379281 q = 1) (hb : d379373 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379281, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379281, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro107658 (p : Pattern) (ha : d379287 p = 1) (hb : d379379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379282 q = 1) (hb : d379374 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379282, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107657 q ha hb
    | true =>
      simp only [d379282, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379283 q = 1) (hb : d379375 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379283, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379283, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379284 q = 1) (hb : d379376 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379284, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379284, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379285 q = 1) (hb : d379377 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379285, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379285, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379286 q = 1) (hb : d379378 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379286, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379286, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379287 q = 1) (hb : d379379 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379287, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379287, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107659 (p : Pattern) (ha : d379293 p = 1) (hb : d379385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379288 q = 1) (hb : d379380 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379288, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107658 q ha hb
    | true =>
      simp only [d379288, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379289 q = 1) (hb : d379381 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379289, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379289, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379290 q = 1) (hb : d379382 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379290, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379290, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379291 q = 1) (hb : d379383 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379291, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379291, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379292 q = 1) (hb : d379384 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379292, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379292, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379293 q = 1) (hb : d379385 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379293, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379293, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107660 (p : Pattern) (ha : d379299 p = 1) (hb : d379391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379294 q = 1) (hb : d379386 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379294, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107659 q ha hb
    | true =>
      simp only [d379294, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379295 q = 1) (hb : d379387 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379295, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379295, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379296 q = 1) (hb : d379388 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379296, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379296, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379297 q = 1) (hb : d379389 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379297, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379297, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379298 q = 1) (hb : d379390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379298, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379298, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379299 q = 1) (hb : d379391 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379299, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379299, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107661 (p : Pattern) (ha : d379305 p = 1) (hb : d379397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379300 q = 1) (hb : d379392 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379300, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107660 q ha hb
    | true =>
      simp only [d379300, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379301 q = 1) (hb : d379393 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379301, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379301, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379302 q = 1) (hb : d379394 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379302, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379302, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379303 q = 1) (hb : d379395 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379303, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379303, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379304 q = 1) (hb : d379396 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379304, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379304, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379305 q = 1) (hb : d379397 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379305, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379305, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107662 (p : Pattern) (ha : d379311 p = 1) (hb : d379403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379306 q = 1) (hb : d379398 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379306, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107661 q ha hb
    | true =>
      simp only [d379306, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379307 q = 1) (hb : d379399 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379307, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379307, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379308 q = 1) (hb : d379400 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379308, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379308, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379309 q = 1) (hb : d379401 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379309, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379309, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379310 q = 1) (hb : d379402 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379310, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379310, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379311 q = 1) (hb : d379403 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379311, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379311, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107663 (p : Pattern) (ha : d379317 p = 1) (hb : d379409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379312 q = 1) (hb : d379404 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379312, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107662 q ha hb
    | true =>
      simp only [d379312, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379313 q = 1) (hb : d379405 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379313, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379313, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379314 q = 1) (hb : d379406 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379314, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379314, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379315 q = 1) (hb : d379407 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379315, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379315, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379316 q = 1) (hb : d379408 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379316, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379316, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379317 q = 1) (hb : d379409 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379317, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379317, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107664 (p : Pattern) (ha : d379323 p = 1) (hb : d379415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379318 q = 1) (hb : d379410 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379318, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107663 q ha hb
    | true =>
      simp only [d379318, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379319 q = 1) (hb : d379411 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379319, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379319, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379320 q = 1) (hb : d379412 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379320, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379320, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379321 q = 1) (hb : d379413 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379321, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379321, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379322 q = 1) (hb : d379414 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379322, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379322, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379323 q = 1) (hb : d379415 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379323, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379323, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107665 (p : Pattern) (ha : d379327 p = 1) (hb : d379373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379324 q = 1) (hb : d379370 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379324, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379324, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d379325 q = 1) (hb : d379371 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379325, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379325, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d379326 q = 1) (hb : d379372 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379326, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379326, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d379327 q = 1) (hb : d379373 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379327, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379327, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro107666 (p : Pattern) (ha : d379333 p = 1) (hb : d379379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379328 q = 1) (hb : d379374 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379328, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107665 q ha hb
    | true =>
      simp only [d379328, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379329 q = 1) (hb : d379375 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379329, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379329, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379330 q = 1) (hb : d379376 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379330, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379330, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379331 q = 1) (hb : d379377 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379331, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379331, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379332 q = 1) (hb : d379378 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379332, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379332, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379333 q = 1) (hb : d379379 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379333, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379333, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107667 (p : Pattern) (ha : d379339 p = 1) (hb : d379385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379334 q = 1) (hb : d379380 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379334, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107666 q ha hb
    | true =>
      simp only [d379334, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379335 q = 1) (hb : d379381 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379335, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379335, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379336 q = 1) (hb : d379382 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379336, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379336, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379337 q = 1) (hb : d379383 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379337, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379337, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379338 q = 1) (hb : d379384 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379338, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379339 q = 1) (hb : d379385 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379339, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107668 (p : Pattern) (ha : d379345 p = 1) (hb : d379391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379340 q = 1) (hb : d379386 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107667 q ha hb
    | true =>
      simp only [d379340, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379341 q = 1) (hb : d379387 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379342 q = 1) (hb : d379388 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379343 q = 1) (hb : d379389 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379344 q = 1) (hb : d379390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379345 q = 1) (hb : d379391 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107669 (p : Pattern) (ha : d379351 p = 1) (hb : d379397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379346 q = 1) (hb : d379392 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107668 q ha hb
    | true =>
      simp only [d379346, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379347 q = 1) (hb : d379393 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379348 q = 1) (hb : d379394 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379349 q = 1) (hb : d379395 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379350 q = 1) (hb : d379396 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379351 q = 1) (hb : d379397 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107670 (p : Pattern) (ha : d379357 p = 1) (hb : d379403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379352 q = 1) (hb : d379398 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107669 q ha hb
    | true =>
      simp only [d379352, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379353 q = 1) (hb : d379399 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379354 q = 1) (hb : d379400 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379355 q = 1) (hb : d379401 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379356 q = 1) (hb : d379402 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379357 q = 1) (hb : d379403 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107671 (p : Pattern) (ha : d379363 p = 1) (hb : d379409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379358 q = 1) (hb : d379404 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107670 q ha hb
    | true =>
      simp only [d379358, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379359 q = 1) (hb : d379405 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379360 q = 1) (hb : d379406 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379361 q = 1) (hb : d379407 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379362 q = 1) (hb : d379408 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379363 q = 1) (hb : d379409 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107672 (p : Pattern) (ha : d379369 p = 1) (hb : d379415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379364 q = 1) (hb : d379410 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107671 q ha hb
    | true =>
      simp only [d379364, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379365 q = 1) (hb : d379411 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379366 q = 1) (hb : d379412 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379367 q = 1) (hb : d379413 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379368 q = 1) (hb : d379414 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379369 q = 1) (hb : d379415 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107673 (p : Pattern) (ha : d379051 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379422 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379047 q = 1) (hb : d379423 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379047, d379423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379047, d379423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379048 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379048, d379424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379048, d379424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379049 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379050 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379051 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107674 (p : Pattern) (ha : d379057 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379052 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107673 q ha hb
    | true =>
      simp only [d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379053 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379054 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379055 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379056 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379057 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107675 (p : Pattern) (ha : d379063 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379058 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107674 q ha hb
    | true =>
      simp only [d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379059 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379060 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379061 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379062 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379063 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107676 (p : Pattern) (ha : d379069 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379064 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107675 q ha hb
    | true =>
      simp only [d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379065 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379066 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379067 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379068 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379069 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107677 (p : Pattern) (ha : d379075 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379070 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107676 q ha hb
    | true =>
      simp only [d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379071 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379072 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379073 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379074 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379075 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107678 (p : Pattern) (ha : d379081 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379076 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107677 q ha hb
    | true =>
      simp only [d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379077 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379078 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379079 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379080 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379081 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107679 (p : Pattern) (ha : d0 p = 1) (hb : d379514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379514 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107680 (p : Pattern) (ha : d379096 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379422 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379092 q = 1) (hb : d379423 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379092, d379423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379092, d379423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379093 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379093, d379424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379093, d379424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379094 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379095 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379096 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107681 (p : Pattern) (ha : d379102 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379097 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107680 q ha hb
    | true =>
      simp only [d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379098 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379099 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379100 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379101 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379102 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107682 (p : Pattern) (ha : d379108 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379103 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107681 q ha hb
    | true =>
      simp only [d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379104 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379105 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379106 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379107 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379108 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107683 (p : Pattern) (ha : d379114 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379109 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107682 q ha hb
    | true =>
      simp only [d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379110 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379111 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379112 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379113 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379114 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107684 (p : Pattern) (ha : d379120 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379115 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107683 q ha hb
    | true =>
      simp only [d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379116 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379117 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379118 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379119 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379120 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107685 (p : Pattern) (ha : d379126 p = 1) (hb : d379424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379121 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107684 q ha hb
    | true =>
      simp only [d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379122 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379123 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379124 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379125 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379126 q = 1) (hb : d379424 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107686 (p : Pattern) (ha : d0 p = 1) (hb : d379559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379559 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107687 (p : Pattern) (ha : d379051 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379047 q = 1) (hb : d379562 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379047, d379562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379047, d379562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379048 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379048, d379563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379048, d379563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379049 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379050 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379051 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107688 (p : Pattern) (ha : d379057 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379052 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107687 q ha hb
    | true =>
      simp only [d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379053 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379054 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379055 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379056 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379057 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107689 (p : Pattern) (ha : d379063 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379058 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107688 q ha hb
    | true =>
      simp only [d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379059 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379060 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379061 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379062 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379063 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107690 (p : Pattern) (ha : d379069 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379064 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107689 q ha hb
    | true =>
      simp only [d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379065 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379066 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379067 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379068 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379069 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107691 (p : Pattern) (ha : d379075 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379070 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107690 q ha hb
    | true =>
      simp only [d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379071 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379072 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379073 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379074 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379075 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107692 (p : Pattern) (ha : d379081 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379076 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107691 q ha hb
    | true =>
      simp only [d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379077 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379078 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379079 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379080 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379081 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107693 (p : Pattern) (ha : d379096 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379092 q = 1) (hb : d379562 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379092, d379562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379092, d379562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379093 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379093, d379563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379093, d379563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379094 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379095 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379096 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107694 (p : Pattern) (ha : d379102 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379097 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107693 q ha hb
    | true =>
      simp only [d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379098 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379099 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379100 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379101 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379102 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107695 (p : Pattern) (ha : d379108 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379103 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107694 q ha hb
    | true =>
      simp only [d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379104 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379105 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379106 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379107 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379108 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107696 (p : Pattern) (ha : d379114 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379109 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107695 q ha hb
    | true =>
      simp only [d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379110 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379111 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379112 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379113 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379114 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107697 (p : Pattern) (ha : d379120 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379115 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107696 q ha hb
    | true =>
      simp only [d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379116 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379117 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379118 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379119 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379120 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107698 (p : Pattern) (ha : d379126 p = 1) (hb : d379563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379121 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107697 q ha hb
    | true =>
      simp only [d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379122 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379123 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379124 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379125 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379126 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107699 (p : Pattern) (ha : d378991 p = 1) (hb : d379081 p = 1) : d379081 p = 1 := by
  have h0 (q : Pattern) (ha : d378991 q = 1) (hb : d379081 q = 1) : d379081 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107700 (p : Pattern) (ha : d375598 p = 1) (hb : d379039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d322203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105123 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d322205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d320183 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d320184 q = 1) (hb : d379037 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d379037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d379037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d375597 q = 1) (hb : d379038 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375597, d379038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d375597, d379038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d375598 q = 1) (hb : d379039 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375598, d379039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d375598, d379039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h10 p ha hb
theorem andIntro107701 (p : Pattern) (ha : d375604 p = 1) (hb : d379045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375599 q = 1) (hb : d379040 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375599, d379040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107700 q ha hb
    | true =>
      simp only [d375599, d379040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375600 q = 1) (hb : d379041 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375600, d379041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375600, d379041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375601 q = 1) (hb : d379042 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375601, d379042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375601, d379042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375602 q = 1) (hb : d379043 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375602, d379043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375602, d379043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375603 q = 1) (hb : d379044 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375603, d379044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375603, d379044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375604 q = 1) (hb : d379045 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375604, d379045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375604, d379045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107702 (p : Pattern) (ha : d375610 p = 1) (hb : d379051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375605 q = 1) (hb : d379046 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375605, d379046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107701 q ha hb
    | true =>
      simp only [d375605, d379046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375606 q = 1) (hb : d379047 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375606, d379047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375606, d379047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375607 q = 1) (hb : d379048 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375607, d379048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375607, d379048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375608 q = 1) (hb : d379049 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375608, d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375608, d379049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375609 q = 1) (hb : d379050 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375609, d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375609, d379050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375610 q = 1) (hb : d379051 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375610, d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375610, d379051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107703 (p : Pattern) (ha : d375616 p = 1) (hb : d379057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375611 q = 1) (hb : d379052 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375611, d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107702 q ha hb
    | true =>
      simp only [d375611, d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375612 q = 1) (hb : d379053 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375612, d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375612, d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375613 q = 1) (hb : d379054 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375613, d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375613, d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375614 q = 1) (hb : d379055 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375614, d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375614, d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375615 q = 1) (hb : d379056 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375615, d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375615, d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375616 q = 1) (hb : d379057 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375616, d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375616, d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107704 (p : Pattern) (ha : d375622 p = 1) (hb : d379063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375617 q = 1) (hb : d379058 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375617, d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107703 q ha hb
    | true =>
      simp only [d375617, d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375618 q = 1) (hb : d379059 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375618, d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375618, d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375619 q = 1) (hb : d379060 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375619, d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375619, d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375620 q = 1) (hb : d379061 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375620, d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375620, d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375621 q = 1) (hb : d379062 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375621, d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375621, d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375622 q = 1) (hb : d379063 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375622, d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375622, d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107705 (p : Pattern) (ha : d375628 p = 1) (hb : d379069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375623 q = 1) (hb : d379064 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375623, d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107704 q ha hb
    | true =>
      simp only [d375623, d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375624 q = 1) (hb : d379065 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375624, d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375624, d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375625 q = 1) (hb : d379066 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375625, d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375625, d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375626 q = 1) (hb : d379067 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375626, d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375626, d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375627 q = 1) (hb : d379068 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375627, d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375627, d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375628 q = 1) (hb : d379069 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375628, d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375628, d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107706 (p : Pattern) (ha : d375634 p = 1) (hb : d379075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375629 q = 1) (hb : d379070 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375629, d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107705 q ha hb
    | true =>
      simp only [d375629, d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375630 q = 1) (hb : d379071 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375630, d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375630, d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375631 q = 1) (hb : d379072 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375631, d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375631, d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375632 q = 1) (hb : d379073 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375632, d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375632, d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375633 q = 1) (hb : d379074 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375633, d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375633, d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375634 q = 1) (hb : d379075 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375634, d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375634, d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107707 (p : Pattern) (ha : d375640 p = 1) (hb : d379081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375635 q = 1) (hb : d379076 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375635, d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107706 q ha hb
    | true =>
      simp only [d375635, d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375636 q = 1) (hb : d379077 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375636, d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375636, d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375637 q = 1) (hb : d379078 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375637, d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375637, d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375638 q = 1) (hb : d379079 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375638, d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375638, d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375639 q = 1) (hb : d379080 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375639, d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375639, d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375640 q = 1) (hb : d379081 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375640, d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375640, d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107708 (p : Pattern) (ha : d378991 p = 1) (hb : d379126 p = 1) : d379126 p = 1 := by
  have h0 (q : Pattern) (ha : d378991 q = 1) (hb : d379126 q = 1) : d379126 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107709 (p : Pattern) (ha : d375598 p = 1) (hb : d379084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105156 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d320183 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d320184 q = 1) (hb : d379082 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d375597 q = 1) (hb : d379083 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375597, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d375597, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d375598 q = 1) (hb : d379084 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375598, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d375598, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h10 p ha hb
theorem andIntro107710 (p : Pattern) (ha : d375604 p = 1) (hb : d379090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375599 q = 1) (hb : d379085 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375599, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107709 q ha hb
    | true =>
      simp only [d375599, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375600 q = 1) (hb : d379086 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375600, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375600, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375601 q = 1) (hb : d379087 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375601, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375601, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375602 q = 1) (hb : d379088 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375602, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375602, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375603 q = 1) (hb : d379089 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375603, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375603, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375604 q = 1) (hb : d379090 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375604, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375604, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107711 (p : Pattern) (ha : d375610 p = 1) (hb : d379096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375605 q = 1) (hb : d379091 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375605, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107710 q ha hb
    | true =>
      simp only [d375605, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375606 q = 1) (hb : d379092 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375606, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375606, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375607 q = 1) (hb : d379093 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375607, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375607, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375608 q = 1) (hb : d379094 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375608, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375608, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375609 q = 1) (hb : d379095 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375609, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375609, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375610 q = 1) (hb : d379096 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375610, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375610, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107712 (p : Pattern) (ha : d375616 p = 1) (hb : d379102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375611 q = 1) (hb : d379097 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375611, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107711 q ha hb
    | true =>
      simp only [d375611, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375612 q = 1) (hb : d379098 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375612, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375612, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375613 q = 1) (hb : d379099 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375613, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375613, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375614 q = 1) (hb : d379100 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375614, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375614, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375615 q = 1) (hb : d379101 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375615, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375615, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375616 q = 1) (hb : d379102 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375616, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375616, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107713 (p : Pattern) (ha : d375622 p = 1) (hb : d379108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375617 q = 1) (hb : d379103 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375617, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107712 q ha hb
    | true =>
      simp only [d375617, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375618 q = 1) (hb : d379104 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375618, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375618, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375619 q = 1) (hb : d379105 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375619, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375619, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375620 q = 1) (hb : d379106 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375620, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375620, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375621 q = 1) (hb : d379107 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375621, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375621, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375622 q = 1) (hb : d379108 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375622, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375622, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107714 (p : Pattern) (ha : d375628 p = 1) (hb : d379114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375623 q = 1) (hb : d379109 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375623, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107713 q ha hb
    | true =>
      simp only [d375623, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375624 q = 1) (hb : d379110 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375624, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375624, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375625 q = 1) (hb : d379111 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375625, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375625, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375626 q = 1) (hb : d379112 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375626, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375626, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375627 q = 1) (hb : d379113 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375627, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375627, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375628 q = 1) (hb : d379114 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375628, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375628, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107715 (p : Pattern) (ha : d375634 p = 1) (hb : d379120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375629 q = 1) (hb : d379115 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375629, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107714 q ha hb
    | true =>
      simp only [d375629, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375630 q = 1) (hb : d379116 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375630, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375630, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375631 q = 1) (hb : d379117 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375631, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375631, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375632 q = 1) (hb : d379118 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375632, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375632, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375633 q = 1) (hb : d379119 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375633, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375633, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375634 q = 1) (hb : d379120 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375634, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375634, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107716 (p : Pattern) (ha : d375640 p = 1) (hb : d379126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375635 q = 1) (hb : d379121 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375635, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107715 q ha hb
    | true =>
      simp only [d375635, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375636 q = 1) (hb : d379122 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375636, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375636, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375637 q = 1) (hb : d379123 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375637, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375637, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375638 q = 1) (hb : d379124 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375638, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375638, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375639 q = 1) (hb : d379125 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375639, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375639, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375640 q = 1) (hb : d379126 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375640, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375640, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107717 (p : Pattern) (ha : d375642 p = 1) (hb : d379084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322203 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105188 q ha hb
  have h5 (q : Pattern) (ha : d322204 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322205 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d322206 q = 1) (hb : d379082 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d322206, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322206, d379082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d375641 q = 1) (hb : d379083 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375641, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d375641, d379083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d375642 q = 1) (hb : d379084 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375642, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d375642, d379084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h10 p ha hb
theorem andIntro107718 (p : Pattern) (ha : d375648 p = 1) (hb : d379090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375643 q = 1) (hb : d379085 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375643, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107717 q ha hb
    | true =>
      simp only [d375643, d379085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375644 q = 1) (hb : d379086 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375644, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375644, d379086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375645 q = 1) (hb : d379087 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375645, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375645, d379087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375646 q = 1) (hb : d379088 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375646, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375646, d379088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375647 q = 1) (hb : d379089 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375647, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375647, d379089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375648 q = 1) (hb : d379090 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375648, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375648, d379090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107719 (p : Pattern) (ha : d375654 p = 1) (hb : d379096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375649 q = 1) (hb : d379091 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375649, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107718 q ha hb
    | true =>
      simp only [d375649, d379091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375650 q = 1) (hb : d379092 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375650, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375650, d379092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375651 q = 1) (hb : d379093 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375651, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375651, d379093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375652 q = 1) (hb : d379094 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375652, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375652, d379094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375653 q = 1) (hb : d379095 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375653, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375653, d379095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375654 q = 1) (hb : d379096 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375654, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375654, d379096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107720 (p : Pattern) (ha : d375660 p = 1) (hb : d379102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375655 q = 1) (hb : d379097 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375655, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107719 q ha hb
    | true =>
      simp only [d375655, d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375656 q = 1) (hb : d379098 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375656, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375656, d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375657 q = 1) (hb : d379099 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375657, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375657, d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375658 q = 1) (hb : d379100 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375658, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375658, d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375659 q = 1) (hb : d379101 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375659, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375659, d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375660 q = 1) (hb : d379102 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375660, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375660, d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107721 (p : Pattern) (ha : d375666 p = 1) (hb : d379108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375661 q = 1) (hb : d379103 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375661, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107720 q ha hb
    | true =>
      simp only [d375661, d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375662 q = 1) (hb : d379104 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375662, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375662, d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375663 q = 1) (hb : d379105 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375663, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375663, d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375664 q = 1) (hb : d379106 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375664, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375664, d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375665 q = 1) (hb : d379107 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375665, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375665, d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375666 q = 1) (hb : d379108 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375666, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375666, d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107722 (p : Pattern) (ha : d375672 p = 1) (hb : d379114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375667 q = 1) (hb : d379109 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375667, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107721 q ha hb
    | true =>
      simp only [d375667, d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375668 q = 1) (hb : d379110 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375668, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375668, d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375669 q = 1) (hb : d379111 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375669, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375669, d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375670 q = 1) (hb : d379112 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375670, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375670, d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375671 q = 1) (hb : d379113 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375671, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375671, d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375672 q = 1) (hb : d379114 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375672, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375672, d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107723 (p : Pattern) (ha : d375678 p = 1) (hb : d379120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375673 q = 1) (hb : d379115 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375673, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107722 q ha hb
    | true =>
      simp only [d375673, d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375674 q = 1) (hb : d379116 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375674, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375674, d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375675 q = 1) (hb : d379117 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375675, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375675, d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375676 q = 1) (hb : d379118 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375676, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375676, d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375677 q = 1) (hb : d379119 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375677, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375677, d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375678 q = 1) (hb : d379120 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375678, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375678, d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107724 (p : Pattern) (ha : d375684 p = 1) (hb : d379126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375679 q = 1) (hb : d379121 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375679, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107723 q ha hb
    | true =>
      simp only [d375679, d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375680 q = 1) (hb : d379122 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375680, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375680, d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375681 q = 1) (hb : d379123 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375681, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375681, d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375682 q = 1) (hb : d379124 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375682, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375682, d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375683 q = 1) (hb : d379125 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375683, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375683, d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375684 q = 1) (hb : d379126 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375684, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375684, d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107725 (p : Pattern) (ha : d379051 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379049 q = 1) (hb : d379575 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379049, d379575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379049, d379575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379050 q = 1) (hb : d379576 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379050, d379576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379050, d379576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d379051 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379051, d379577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379051, d379577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro107726 (p : Pattern) (ha : d379057 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379052 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107725 q ha hb
    | true =>
      simp only [d379052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379053 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379054 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379055 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379056 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379057 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107727 (p : Pattern) (ha : d379063 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379058 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107726 q ha hb
    | true =>
      simp only [d379058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379059 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379060 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379061 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379062 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379063 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107728 (p : Pattern) (ha : d379069 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379064 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107727 q ha hb
    | true =>
      simp only [d379064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379065 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379066 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379067 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379068 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379069 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107729 (p : Pattern) (ha : d379075 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379070 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107728 q ha hb
    | true =>
      simp only [d379070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379071 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379072 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379073 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379074 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379075 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107730 (p : Pattern) (ha : d379081 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379076 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107729 q ha hb
    | true =>
      simp only [d379076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379077 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379078 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379079 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379080 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379081 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107731 (p : Pattern) (ha : d379096 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379094 q = 1) (hb : d379575 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379094, d379575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379094, d379575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379095 q = 1) (hb : d379576 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379095, d379576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379095, d379576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d379096 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379096, d379577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379096, d379577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro107732 (p : Pattern) (ha : d379102 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379097 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107731 q ha hb
    | true =>
      simp only [d379097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379098 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379099 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379100 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379101 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379102 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107733 (p : Pattern) (ha : d379108 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379103 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107732 q ha hb
    | true =>
      simp only [d379103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379104 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379105 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379106 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379107 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379108 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107734 (p : Pattern) (ha : d379114 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379109 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107733 q ha hb
    | true =>
      simp only [d379109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379110 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379111 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379112 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379113 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379114 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107735 (p : Pattern) (ha : d379120 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379115 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107734 q ha hb
    | true =>
      simp only [d379115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379116 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379117 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379118 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379119 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379120 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107736 (p : Pattern) (ha : d379126 p = 1) (hb : d379577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379121 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107735 q ha hb
    | true =>
      simp only [d379121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379122 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379123 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379124 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379125 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379126 q = 1) (hb : d379577 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107737 (p : Pattern) (ha : d379327 p = 1) (hb : d379581 p = 1) : d379635 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322122 q = 1) : d322122 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322163 q = 1) (hb : d364936 q = 1) : d379631 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d364936, d379631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322163, d364936, d379631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379324 q = 1) (hb : d379581 q = 1) : d379632 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379324, d379581, d379632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379324, d379581, d379632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379581 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379325 q = 1) (hb : d379581 q = 1) : d379633 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379325, d379633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379325, d379633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379326 q = 1) (hb : d379581 q = 1) : d379634 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379326, d379634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379326, d379634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379327 q = 1) (hb : d379581 q = 1) : d379635 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379327, d379635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379327, d379635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107738 (p : Pattern) (ha : d379333 p = 1) (hb : d379581 p = 1) : d379641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379328 q = 1) (hb : d379581 q = 1) : d379636 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379328, d379636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107737 q ha hb
    | true =>
      simp only [d379328, d379636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379329 q = 1) (hb : d379581 q = 1) : d379637 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379329, d379637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379329, d379637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379330 q = 1) (hb : d379581 q = 1) : d379638 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379330, d379638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379330, d379638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379331 q = 1) (hb : d379581 q = 1) : d379639 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379331, d379639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379331, d379639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379332 q = 1) (hb : d379581 q = 1) : d379640 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379332, d379640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379332, d379640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379333 q = 1) (hb : d379581 q = 1) : d379641 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379333, d379641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379333, d379641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107739 (p : Pattern) (ha : d379339 p = 1) (hb : d379583 p = 1) : d379647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379334 q = 1) (hb : d379582 q = 1) : d379642 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379334, d379582, d379642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107738 q ha hb
    | true =>
      simp only [d379334, d379582, d379642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379335 q = 1) (hb : d379583 q = 1) : d379643 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379335, d379583, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379335, d379583, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379336 q = 1) (hb : d379583 q = 1) : d379644 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379336, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379336, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d379337 q = 1) (hb : d379583 q = 1) : d379645 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379337, d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379337, d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d379338 q = 1) (hb : d379583 q = 1) : d379646 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379338, d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d379339 q = 1) (hb : d379583 q = 1) : d379647 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379339, d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro107740 (p : Pattern) (ha : d379345 p = 1) (hb : d379583 p = 1) : d379653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379340 q = 1) (hb : d379583 q = 1) : d379648 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107739 q ha hb
    | true =>
      simp only [d379340, d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379341 q = 1) (hb : d379583 q = 1) : d379649 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379342 q = 1) (hb : d379583 q = 1) : d379650 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379343 q = 1) (hb : d379583 q = 1) : d379651 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379344 q = 1) (hb : d379583 q = 1) : d379652 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379345 q = 1) (hb : d379583 q = 1) : d379653 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107741 (p : Pattern) (ha : d379351 p = 1) (hb : d379583 p = 1) : d379659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379346 q = 1) (hb : d379583 q = 1) : d379654 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107740 q ha hb
    | true =>
      simp only [d379346, d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379347 q = 1) (hb : d379583 q = 1) : d379655 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379348 q = 1) (hb : d379583 q = 1) : d379656 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379349 q = 1) (hb : d379583 q = 1) : d379657 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379350 q = 1) (hb : d379583 q = 1) : d379658 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379351 q = 1) (hb : d379583 q = 1) : d379659 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107742 (p : Pattern) (ha : d379357 p = 1) (hb : d379583 p = 1) : d379665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379352 q = 1) (hb : d379583 q = 1) : d379660 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107741 q ha hb
    | true =>
      simp only [d379352, d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379353 q = 1) (hb : d379583 q = 1) : d379661 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379354 q = 1) (hb : d379583 q = 1) : d379662 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379355 q = 1) (hb : d379583 q = 1) : d379663 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379356 q = 1) (hb : d379583 q = 1) : d379664 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379357 q = 1) (hb : d379583 q = 1) : d379665 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107743 (p : Pattern) (ha : d379363 p = 1) (hb : d379583 p = 1) : d379671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379358 q = 1) (hb : d379583 q = 1) : d379666 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107742 q ha hb
    | true =>
      simp only [d379358, d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379359 q = 1) (hb : d379583 q = 1) : d379667 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379360 q = 1) (hb : d379583 q = 1) : d379668 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379361 q = 1) (hb : d379583 q = 1) : d379669 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379362 q = 1) (hb : d379583 q = 1) : d379670 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379363 q = 1) (hb : d379583 q = 1) : d379671 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107744 (p : Pattern) (ha : d379369 p = 1) (hb : d379583 p = 1) : d379677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379364 q = 1) (hb : d379583 q = 1) : d379672 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107743 q ha hb
    | true =>
      simp only [d379364, d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379365 q = 1) (hb : d379583 q = 1) : d379673 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379366 q = 1) (hb : d379583 q = 1) : d379674 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379367 q = 1) (hb : d379583 q = 1) : d379675 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379368 q = 1) (hb : d379583 q = 1) : d379676 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379369 q = 1) (hb : d379583 q = 1) : d379677 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107745 (p : Pattern) (ha : d379588 p = 1) (hb : d379635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379584 q = 1) (hb : d379631 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379584, d379631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379584, d379631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d379585 q = 1) (hb : d379632 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379585, d379632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379585, d379632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d379586 q = 1) (hb : d379633 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379586, d379633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379586, d379633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d379587 q = 1) (hb : d379634 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379587, d379634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379587, d379634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d379588 q = 1) (hb : d379635 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379588, d379635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379588, d379635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h6 p ha hb
theorem andIntro107746 (p : Pattern) (ha : d379594 p = 1) (hb : d379641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379589 q = 1) (hb : d379636 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379589, d379636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107745 q ha hb
    | true =>
      simp only [d379589, d379636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379590 q = 1) (hb : d379637 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379590, d379637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379590, d379637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379591 q = 1) (hb : d379638 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379591, d379638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379591, d379638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379592 q = 1) (hb : d379639 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379592, d379639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379592, d379639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379593 q = 1) (hb : d379640 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379593, d379640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379593, d379640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379594 q = 1) (hb : d379641 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379594, d379641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379594, d379641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107747 (p : Pattern) (ha : d379600 p = 1) (hb : d379647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379595 q = 1) (hb : d379642 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379595, d379642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107746 q ha hb
    | true =>
      simp only [d379595, d379642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379596 q = 1) (hb : d379643 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379596, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379596, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379597 q = 1) (hb : d379644 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379597, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379597, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379598 q = 1) (hb : d379645 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379598, d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379598, d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379599 q = 1) (hb : d379646 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379599, d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379599, d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379600 q = 1) (hb : d379647 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379600, d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379600, d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107748 (p : Pattern) (ha : d379606 p = 1) (hb : d379653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379601 q = 1) (hb : d379648 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379601, d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107747 q ha hb
    | true =>
      simp only [d379601, d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379602 q = 1) (hb : d379649 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379602, d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379602, d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379603 q = 1) (hb : d379650 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379603, d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379603, d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379604 q = 1) (hb : d379651 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379604, d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379604, d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379605 q = 1) (hb : d379652 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379605, d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379605, d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379606 q = 1) (hb : d379653 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379606, d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379606, d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107749 (p : Pattern) (ha : d379612 p = 1) (hb : d379659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379607 q = 1) (hb : d379654 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379607, d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107748 q ha hb
    | true =>
      simp only [d379607, d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379608 q = 1) (hb : d379655 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379608, d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379608, d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379609 q = 1) (hb : d379656 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379609, d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379609, d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379610 q = 1) (hb : d379657 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379610, d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379610, d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379611 q = 1) (hb : d379658 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379611, d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379611, d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379612 q = 1) (hb : d379659 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379612, d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379612, d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
