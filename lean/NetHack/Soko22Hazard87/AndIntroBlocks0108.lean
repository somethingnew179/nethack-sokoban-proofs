import NetHack.Soko22Hazard87.AndIntroBlocks0107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro27000 (p : Pattern) (ha : d145673 p = 1) (hb : d146672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143325 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145659 q = 1) (hb : d146663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145659, d146663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145659, d146663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d143382 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145660 q = 1) (hb : d146664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145660, d146664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145660, d146664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145661 q = 1) (hb : d146665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145661, d146665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145661, d146665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145662 q = 1) (hb : d146666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145662, d146666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145662, d146666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d143392 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d143397 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d143399 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d145668 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d145669 q = 1) (hb : d146668 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145669, d146668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145669, d146668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143406 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145670 q = 1) (hb : d146669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145670, d146669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145670, d146669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145671 q = 1) (hb : d146670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145671, d146670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145671, d146670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145672 q = 1) (hb : d146671 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145672, d146671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145672, d146671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145673 q = 1) (hb : d146672 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145673, d146672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145673, d146672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27001 (p : Pattern) (ha : d146412 p = 1) (hb : d146679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143399 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145668 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145669 q = 1) (hb : d146668 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145669, d146668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145669, d146668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143406 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145670 q = 1) (hb : d146669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145670, d146669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145670, d146669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145671 q = 1) (hb : d146677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145671, d146677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145671, d146677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145672 q = 1) (hb : d146678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145672, d146678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145672, d146678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146412 q = 1) (hb : d146679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146412, d146679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146412, d146679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27002 (p : Pattern) (ha : d146423 p = 1) (hb : d146689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143473 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146419 q = 1) (hb : d146685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146419, d146685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146419, d146685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143505 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146420 q = 1) (hb : d146686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146420, d146686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146420, d146686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146421 q = 1) (hb : d146687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146421, d146687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146421, d146687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146422 q = 1) (hb : d146688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146422, d146688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146422, d146688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146423 q = 1) (hb : d146689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146423, d146689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146423, d146689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27003 (p : Pattern) (ha : d146429 p = 1) (hb : d146695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145674 q = 1) (hb : d146673 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145674, d146673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26999 q ha hb
    | true =>
      simp only [d145674, d146673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27000 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145675 q = 1) (hb : d146674 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145675, d146674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145675, d146674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146410 q = 1) (hb : d146675 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146410, d146675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146410, d146675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146411 q = 1) (hb : d146676 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146411, d146676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146411, d146676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146413 q = 1) (hb : d146680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146413, d146680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146413, d146680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27001 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d143433 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146414 q = 1) (hb : d146681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146414, d146681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146414, d146681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146415 q = 1) (hb : d146682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146415, d146682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146415, d146682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d146416 q = 1) (hb : d146683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146416, d146683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146416, d146683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d146417 q = 1) (hb : d146684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146417, d146684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146417, d146684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146424 q = 1) (hb : d146690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146424, d146690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146424, d146690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27002 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143521 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146425 q = 1) (hb : d146691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146425, d146691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146425, d146691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146426 q = 1) (hb : d146692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146426, d146692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146426, d146692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d146427 q = 1) (hb : d146693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146427, d146693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146427, d146693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d146428 q = 1) (hb : d146694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146428, d146694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146428, d146694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d146429 q = 1) (hb : d146695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146429, d146695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146429, d146695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27004 (p : Pattern) (ha : d146435 p = 1) (hb : d146701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146430 q = 1) (hb : d146696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146430, d146696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146430, d146696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27003 q ha hb
  have h2 (q : Pattern) (ha : d146431 q = 1) (hb : d146697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146431, d146697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146431, d146697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146432 q = 1) (hb : d146698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146432, d146698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146432, d146698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146433 q = 1) (hb : d146699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146433, d146699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146433, d146699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146434 q = 1) (hb : d146700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146434, d146700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146434, d146700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146435 q = 1) (hb : d146701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d146435, d146701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146435, d146701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27005 (p : Pattern) (ha : d145889 p = 1) (hb : d146709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143586 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143595 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d143611 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145885 q = 1) (hb : d146705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145885, d146705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145885, d146705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d143643 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145886 q = 1) (hb : d146706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145886, d146706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145886, d146706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145887 q = 1) (hb : d146707 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145887, d146707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145887, d146707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145888 q = 1) (hb : d146708 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145888, d146708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145888, d146708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145889 q = 1) (hb : d146709 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145889, d146709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145889, d146709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27006 (p : Pattern) (ha : d145899 p = 1) (hb : d146714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145885 q = 1) (hb : d146705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145885, d146705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145885, d146705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d143643 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145886 q = 1) (hb : d146706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145886, d146706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145886, d146706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145887 q = 1) (hb : d146707 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145887, d146707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145887, d146707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145888 q = 1) (hb : d146708 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145888, d146708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145888, d146708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d143653 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d143658 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d143660 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d145894 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d145895 q = 1) (hb : d146710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145895, d146710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145895, d146710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143667 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145896 q = 1) (hb : d146711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145896, d146711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145896, d146711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145897 q = 1) (hb : d146712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145897, d146712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145897, d146712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145898 q = 1) (hb : d146713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145898, d146713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145898, d146713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145899 q = 1) (hb : d146714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145899, d146714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145899, d146714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27007 (p : Pattern) (ha : d146441 p = 1) (hb : d146721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143660 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145895 q = 1) (hb : d146710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145895, d146710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145895, d146710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143667 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145896 q = 1) (hb : d146711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145896, d146711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145896, d146711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145897 q = 1) (hb : d146719 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145897, d146719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145897, d146719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145898 q = 1) (hb : d146720 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145898, d146720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145898, d146720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146441 q = 1) (hb : d146721 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146441, d146721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146441, d146721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27008 (p : Pattern) (ha : d146452 p = 1) (hb : d146731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146447 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146448 q = 1) (hb : d146727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146448, d146727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146448, d146727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143766 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146449 q = 1) (hb : d146728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146449, d146728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146449, d146728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146450 q = 1) (hb : d146729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146450, d146729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146450, d146729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146451 q = 1) (hb : d146730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146451, d146730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146451, d146730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146452 q = 1) (hb : d146731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146452, d146731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146452, d146731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27009 (p : Pattern) (ha : d146458 p = 1) (hb : d146737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143578 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145900 q = 1) (hb : d146715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145900, d146715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27005 q ha hb
    | true =>
      simp only [d145900, d146715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27006 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145901 q = 1) (hb : d146716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145901, d146716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145901, d146716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146439 q = 1) (hb : d146717 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146439, d146717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146439, d146717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146440 q = 1) (hb : d146718 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146440, d146718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146440, d146718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146442 q = 1) (hb : d146722 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146442, d146722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146442, d146722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27007 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d143694 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146443 q = 1) (hb : d146723 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146443, d146723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146443, d146723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146444 q = 1) (hb : d146724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146444, d146724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146444, d146724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d146445 q = 1) (hb : d146725 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146445, d146725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146445, d146725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d146446 q = 1) (hb : d146726 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146446, d146726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146446, d146726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146453 q = 1) (hb : d146732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146453, d146732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146453, d146732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27008 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146454 q = 1) (hb : d146733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146454, d146733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146454, d146733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146455 q = 1) (hb : d146734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146455, d146734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146455, d146734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d146456 q = 1) (hb : d146735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146456, d146735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146456, d146735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d146457 q = 1) (hb : d146736 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146457, d146736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146457, d146736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d146458 q = 1) (hb : d146737 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146458, d146737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146458, d146737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27010 (p : Pattern) (ha : d146464 p = 1) (hb : d146743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146459 q = 1) (hb : d146738 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146459, d146738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146459, d146738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27009 q ha hb
  have h2 (q : Pattern) (ha : d146460 q = 1) (hb : d146739 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146460, d146739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146460, d146739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146461 q = 1) (hb : d146740 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146461, d146740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146461, d146740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146462 q = 1) (hb : d146741 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146462, d146741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146462, d146741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146463 q = 1) (hb : d146742 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146463, d146742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146463, d146742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146464 q = 1) (hb : d146743 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d146464, d146743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146464, d146743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27011 (p : Pattern) (ha : d146116 p = 1) (hb : d146752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143848 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d143873 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146112 q = 1) (hb : d146748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146112, d146748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146112, d146748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d143905 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146113 q = 1) (hb : d146749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146113, d146749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146113, d146749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146114 q = 1) (hb : d146750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146114, d146750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146114, d146750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146115 q = 1) (hb : d146751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146115, d146751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146115, d146751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146116 q = 1) (hb : d146752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146116, d146752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146116, d146752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27012 (p : Pattern) (ha : d146126 p = 1) (hb : d146757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143848 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143857 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d146112 q = 1) (hb : d146748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146112, d146748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146112, d146748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d143905 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146113 q = 1) (hb : d146749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146113, d146749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146113, d146749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146114 q = 1) (hb : d146750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146114, d146750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146114, d146750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146115 q = 1) (hb : d146751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146115, d146751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146115, d146751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d143915 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d143920 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d143922 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d146121 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d146122 q = 1) (hb : d146753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146122, d146753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146122, d146753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143929 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146123 q = 1) (hb : d146754 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146123, d146754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146123, d146754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146124 q = 1) (hb : d146755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146124, d146755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146124, d146755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146125 q = 1) (hb : d146756 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146125, d146756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146125, d146756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146126 q = 1) (hb : d146757 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146126, d146757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146126, d146757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27013 (p : Pattern) (ha : d146471 p = 1) (hb : d146764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146122 q = 1) (hb : d146753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146122, d146753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146122, d146753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146123 q = 1) (hb : d146754 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146123, d146754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146123, d146754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146124 q = 1) (hb : d146762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146124, d146762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146124, d146762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146125 q = 1) (hb : d146763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146125, d146763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146125, d146763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146471 q = 1) (hb : d146764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146471, d146764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146471, d146764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27014 (p : Pattern) (ha : d146482 p = 1) (hb : d146774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146478 q = 1) (hb : d146770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146478, d146770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146478, d146770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146479 q = 1) (hb : d146771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146479, d146771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146479, d146771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146480 q = 1) (hb : d146772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146480, d146772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146480, d146772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146481 q = 1) (hb : d146773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146481, d146773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146481, d146773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146482 q = 1) (hb : d146774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146482, d146774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146482, d146774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27015 (p : Pattern) (ha : d146488 p = 1) (hb : d146780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143840 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146127 q = 1) (hb : d146758 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146127, d146758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27011 q ha hb
    | true =>
      simp only [d146127, d146758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27012 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146128 q = 1) (hb : d146759 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146128, d146759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146128, d146759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146469 q = 1) (hb : d146760 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146469, d146760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146469, d146760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146470 q = 1) (hb : d146761 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146470, d146761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146470, d146761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146472 q = 1) (hb : d146765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146472, d146765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146472, d146765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27013 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d143956 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146473 q = 1) (hb : d146766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146473, d146766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146473, d146766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146474 q = 1) (hb : d146767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146474, d146767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146474, d146767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d146475 q = 1) (hb : d146768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146475, d146768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146475, d146768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d146476 q = 1) (hb : d146769 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146476, d146769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146476, d146769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146483 q = 1) (hb : d146775 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146483, d146775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146483, d146775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27014 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144044 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146484 q = 1) (hb : d146776 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146484, d146776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146484, d146776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146485 q = 1) (hb : d146777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146485, d146777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146485, d146777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d146486 q = 1) (hb : d146778 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146486, d146778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146486, d146778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d146487 q = 1) (hb : d146779 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146487, d146779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146487, d146779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d146488 q = 1) (hb : d146780 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146488, d146780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146488, d146780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27016 (p : Pattern) (ha : d146494 p = 1) (hb : d146786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146489 q = 1) (hb : d146781 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146489, d146781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146489, d146781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27015 q ha hb
  have h2 (q : Pattern) (ha : d146490 q = 1) (hb : d146782 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146490, d146782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146490, d146782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146491 q = 1) (hb : d146783 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146491, d146783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146491, d146783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146492 q = 1) (hb : d146784 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146492, d146784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146492, d146784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146493 q = 1) (hb : d146785 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146493, d146785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146493, d146785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146494 q = 1) (hb : d146786 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d146494, d146786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146494, d146786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27017 (p : Pattern) (ha : d146500 p = 1) (hb : d146792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d146381 q = 1) (hb : d146621 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d146381, d146621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26986 q ha hb
    | true =>
      simp only [d146381, d146621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26992 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146408 q = 1) (hb : d146661 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d146408, d146661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146408, d146661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26998 q ha hb
  have h3 (q : Pattern) (ha : d146409 q = 1) (hb : d146662 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d146409, d146662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146409, d146662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146436 q = 1) (hb : d146702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d146436, d146702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146436, d146702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27004 q ha hb
  have h5 (q : Pattern) (ha : d146437 q = 1) (hb : d146703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d146437, d146703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146437, d146703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146438 q = 1) (hb : d146704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d146438, d146704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146438, d146704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146465 q = 1) (hb : d146744 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d146465, d146744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146465, d146744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27010 q ha hb
  have h8 (q : Pattern) (ha : d146466 q = 1) (hb : d146745 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d146466, d146745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146466, d146745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146467 q = 1) (hb : d146746 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d146467, d146746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146467, d146746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146468 q = 1) (hb : d146747 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d146468, d146747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146468, d146747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146495 q = 1) (hb : d146787 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d146495, d146787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146495, d146787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27016 q ha hb
  have h12 (q : Pattern) (ha : d146496 q = 1) (hb : d146788 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d146496, d146788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146496, d146788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146497 q = 1) (hb : d146789 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d146497, d146789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146497, d146789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146498 q = 1) (hb : d146790 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d146498, d146790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146498, d146790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146499 q = 1) (hb : d146791 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d146499, d146791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146499, d146791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146500 q = 1) (hb : d146792 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d146500, d146792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146500, d146792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro27018 (p : Pattern) (ha : d146506 p = 1) (hb : d146798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146501 q = 1) (hb : d146793 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d146501, d146793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27017 q ha hb
    | true =>
      simp only [d146501, d146793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146502 q = 1) (hb : d146794 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d146502, d146794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146502, d146794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146503 q = 1) (hb : d146795 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d146503, d146795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146503, d146795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146504 q = 1) (hb : d146796 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d146504, d146796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146504, d146796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146505 q = 1) (hb : d146797 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d146505, d146797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146505, d146797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146506 q = 1) (hb : d146798 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d146506, d146798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146506, d146798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27019 (p : Pattern) (ha : d146512 p = 1) (hb : d146804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146507 q = 1) (hb : d146799 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d146507, d146799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27018 q ha hb
    | true =>
      simp only [d146507, d146799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146508 q = 1) (hb : d146800 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d146508, d146800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146508, d146800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146509 q = 1) (hb : d146801 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d146509, d146801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146509, d146801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146510 q = 1) (hb : d146802 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d146510, d146802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146510, d146802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146511 q = 1) (hb : d146803 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d146511, d146803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146511, d146803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146512 q = 1) (hb : d146804 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d146512, d146804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146512, d146804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27020 (p : Pattern) (ha : d146518 p = 1) (hb : d146810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146513 q = 1) (hb : d146805 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d146513, d146805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27019 q ha hb
    | true =>
      simp only [d146513, d146805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146514 q = 1) (hb : d146806 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d146514, d146806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146514, d146806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146515 q = 1) (hb : d146807 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d146515, d146807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146515, d146807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146516 q = 1) (hb : d146808 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d146516, d146808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146516, d146808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146517 q = 1) (hb : d146809 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d146517, d146809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146517, d146809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146518 q = 1) (hb : d146810 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d146518, d146810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146518, d146810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27021 (p : Pattern) (ha : d146524 p = 1) (hb : d146816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146519 q = 1) (hb : d146811 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d146519, d146811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27020 q ha hb
    | true =>
      simp only [d146519, d146811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146520 q = 1) (hb : d146812 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d146520, d146812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146520, d146812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146521 q = 1) (hb : d146813 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d146521, d146813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146521, d146813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146522 q = 1) (hb : d146814 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d146522, d146814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146522, d146814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146523 q = 1) (hb : d146815 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d146523, d146815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146523, d146815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146524 q = 1) (hb : d146816 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d146524, d146816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146524, d146816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27022 (p : Pattern) (ha : d146530 p = 1) (hb : d146822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146525 q = 1) (hb : d146817 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d146525, d146817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27021 q ha hb
    | true =>
      simp only [d146525, d146817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146526 q = 1) (hb : d146818 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d146526, d146818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146526, d146818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146527 q = 1) (hb : d146819 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d146527, d146819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146527, d146819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146528 q = 1) (hb : d146820 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d146528, d146820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146528, d146820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146529 q = 1) (hb : d146821 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d146529, d146821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146529, d146821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146530 q = 1) (hb : d146822 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d146530, d146822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146530, d146822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27023 (p : Pattern) (ha : d146536 p = 1) (hb : d146828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146531 q = 1) (hb : d146823 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d146531, d146823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27022 q ha hb
    | true =>
      simp only [d146531, d146823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146532 q = 1) (hb : d146824 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d146532, d146824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146532, d146824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146533 q = 1) (hb : d146825 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d146533, d146825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146533, d146825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146534 q = 1) (hb : d146826 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d146534, d146826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146534, d146826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146535 q = 1) (hb : d146827 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d146535, d146827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146535, d146827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146536 q = 1) (hb : d146828 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d146536, d146828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146536, d146828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27024 (p : Pattern) (ha : d146542 p = 1) (hb : d146834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146537 q = 1) (hb : d146829 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d146537, d146829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27023 q ha hb
    | true =>
      simp only [d146537, d146829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d146538 q = 1) (hb : d146830 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d146538, d146830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146538, d146830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146539 q = 1) (hb : d146831 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d146539, d146831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146539, d146831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d146540 q = 1) (hb : d146832 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d146540, d146832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146540, d146832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146541 q = 1) (hb : d146833 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d146541, d146833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146541, d146833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d146542 q = 1) (hb : d146834 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d146542, d146834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146542, d146834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27025 (p : Pattern) (ha : d109109 p = 1) (hb : d135429 p = 1) : d109109 p = 1 := by
  have h0 (q : Pattern) (ha : d109109 q = 1) (hb : d135429 q = 1) : d109109 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro27026 (p : Pattern) (ha : d10654 p = 1) (hb : d52001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10652 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10653 q = 1) (hb : d52000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10653, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10654 q = 1) (hb : d52001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10654, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27027 (p : Pattern) (ha : d10660 p = 1) (hb : d52007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10660 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27028 (p : Pattern) (ha : d52013 p = 1) (hb : d108784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d108780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d108781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d108782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d108783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52013 q = 1) (hb : d108784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d108784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d108784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27029 (p : Pattern) (ha : d10667 p = 1) (hb : d52023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10667 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10667, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27030 (p : Pattern) (ha : d52029 p = 1) (hb : d108789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d108780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d108781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d108782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d108783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d10668 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
    | true =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52025 q = 1) (hb : d108785 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52025, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d52026 q = 1) (hb : d108786 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d52026, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d52027 q = 1) (hb : d108787 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d108787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52027, d108787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d52028 q = 1) (hb : d108788 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d108788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d52028, d108788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d52029 q = 1) (hb : d108789 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d108789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52029, d108789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27031 (p : Pattern) (ha : d52038 p = 1) (hb : d108796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10668 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
    | true =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52025 q = 1) (hb : d108785 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52025, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52026 q = 1) (hb : d108786 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52026, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52036 q = 1) (hb : d108794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d108794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d108794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52037 q = 1) (hb : d108795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d108795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d108795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52038 q = 1) (hb : d108796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d108796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d108796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27032 (p : Pattern) (ha : d10691 p = 1) (hb : d52055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10689 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10690 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10690, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10691 q = 1) (hb : d52055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10691, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27033 (p : Pattern) (ha : d10697 p = 1) (hb : d52061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27032 q ha hb
    | true =>
      simp only [d10692, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10694 q = 1) (hb : d52058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10695 q = 1) (hb : d52059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10695, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10696 q = 1) (hb : d52060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10696, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10697 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10697, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27034 (p : Pattern) (ha : d52067 p = 1) (hb : d108806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10698 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27033 q ha hb
    | true =>
      simp only [d10698, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d108802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d108802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52063, d108802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d108803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d108803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d108803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d108804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d108804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d108804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d108805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d108805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d108805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d108806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d108806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d108806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27035 (p : Pattern) (ha : d52073 p = 1) (hb : d108812 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d52030 q = 1) (hb : d108790 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d108790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27028 q ha hb
    | true =>
      simp only [d52030, d108790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27030 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d108791 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d108791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52033, d108791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d108792 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d108792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d108792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d108793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d108793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d108793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52039 q = 1) (hb : d108797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d108797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52039, d108797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27031 q ha hb
  have h12 (q : Pattern) (ha : d52040 q = 1) (hb : d108798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d108798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52040, d108798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52041 q = 1) (hb : d108799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d108799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52041, d108799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52042 q = 1) (hb : d108800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d108800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52042, d108800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d108801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d108801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d108801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52068 q = 1) (hb : d108807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d108807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52068, d108807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27034 q ha hb
  have h17 (q : Pattern) (ha : d52069 q = 1) (hb : d108808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d108808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52069, d108808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52070 q = 1) (hb : d108809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d108809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52070, d108809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52071 q = 1) (hb : d108810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d108810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52071, d108810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52072 q = 1) (hb : d108811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d108811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d52072, d108811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d108812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d108812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d108812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro27036 (p : Pattern) (ha : d10719 p = 1) (hb : d52083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10719 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27037 (p : Pattern) (ha : d10726 p = 1) (hb : d52090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10668 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
    | true =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d10722 q = 1) (hb : d52086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10723 q = 1) (hb : d52087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10723, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10724 q = 1) (hb : d52088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10725 q = 1) (hb : d52089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10726 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10726, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27038 (p : Pattern) (ha : d10801 p = 1) (hb : d52163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10801 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10801, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27039 (p : Pattern) (ha : d10731 p = 1) (hb : d52095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10731 q = 1) (hb : d52095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27040 (p : Pattern) (ha : d10738 p = 1) (hb : d52102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10738 q = 1) (hb : d52102 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27041 (p : Pattern) (ha : d10747 p = 1) (hb : d52129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10745 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10652 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10746 q = 1) (hb : d52128 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d52128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10746, d52128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10747 q = 1) (hb : d52129 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d52129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10747, d52129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro27042 (p : Pattern) (ha : d10753 p = 1) (hb : d52135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27041 q ha hb
    | true =>
      simp only [d10748, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d52135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d52135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d52135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27043 (p : Pattern) (ha : d10772 p = 1) (hb : d68835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d68835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27044 (p : Pattern) (ha : d74080 p = 1) (hb : d108822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27039 q ha hb
    | true =>
      simp only [d10732, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27040 q ha hb
    | true =>
      simp only [d10739, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27042 q ha hb
    | true =>
      simp only [d10754, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52137 q = 1) (hb : d108818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52137, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10773 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27043 q ha hb
    | true =>
      simp only [d10773, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10774 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10774, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d108819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74077, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d108820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74078, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d108821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74079, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74080 q = 1) (hb : d108822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74080, d108822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74080, d108822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27045 (p : Pattern) (ha : d10779 p = 1) (hb : d52144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10779 q = 1) (hb : d52144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10779, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27046 (p : Pattern) (ha : d10784 p = 1) (hb : d52149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10784 q = 1) (hb : d52149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10784, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27047 (p : Pattern) (ha : d10788 p = 1) (hb : d52153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27041 q ha hb
    | true =>
      simp only [d10748, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d52153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d52153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d52153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27048 (p : Pattern) (ha : d10793 p = 1) (hb : d74081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27026 q ha hb
    | true =>
      simp only [d10655, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d74081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27049 (p : Pattern) (ha : d74087 p = 1) (hb : d108827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27039 q ha hb
    | true =>
      simp only [d10732, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27040 q ha hb
    | true =>
      simp only [d10739, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27042 q ha hb
    | true =>
      simp only [d10754, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52137 q = 1) (hb : d108818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52137, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10773 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27043 q ha hb
    | true =>
      simp only [d10773, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10774 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10774, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d108819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74077, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d108820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74078, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d108821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74079, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10780 q = 1) (hb : d52145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27045 q ha hb
    | true =>
      simp only [d10780, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d10781 q = 1) (hb : d52146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10782 q = 1) (hb : d52147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10782, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10783 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10785 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27046 q ha hb
    | true =>
      simp only [d10785, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d10786 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10787 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10787, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d10789 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27047 q ha hb
    | true =>
      simp only [d10789, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52155 q = 1) (hb : d108823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52155, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10794 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27048 q ha hb
    | true =>
      simp only [d10794, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10795 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10795, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74084 q = 1) (hb : d108824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74084, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74085 q = 1) (hb : d108825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74085, d108825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74085, d108825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74086 q = 1) (hb : d108826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74086, d108826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74086, d108826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74087 q = 1) (hb : d108827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74087, d108827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74087, d108827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27050 (p : Pattern) (ha : d74094 p = 1) (hb : d108834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27047 q ha hb
    | true =>
      simp only [d10789, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52155 q = 1) (hb : d108823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52155, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10794 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27048 q ha hb
    | true =>
      simp only [d10794, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10795 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10795, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74084 q = 1) (hb : d108824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74084, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74092 q = 1) (hb : d108832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74092, d108832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74092, d108832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74093 q = 1) (hb : d108833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74093, d108833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74093, d108833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74094 q = 1) (hb : d108834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d108834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d108834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27051 (p : Pattern) (ha : d10819 p = 1) (hb : d52189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10817 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10689 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10818 q = 1) (hb : d52188 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d52188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10818, d52188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10819 q = 1) (hb : d52189 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d52189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10819, d52189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro27052 (p : Pattern) (ha : d10825 p = 1) (hb : d52195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d52190 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27051 q ha hb
    | true =>
      simp only [d10820, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d52191 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27032 q ha hb
    | true =>
      simp only [d10692, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d52192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d52192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d52192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d52193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d52193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d52193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d52194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d52194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d52194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d52195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d52195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d52195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27053 (p : Pattern) (ha : d10844 p = 1) (hb : d74103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27032 q ha hb
    | true =>
      simp only [d10692, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d74100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d74101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d74102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d74103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27054 (p : Pattern) (ha : d74109 p = 1) (hb : d108844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27052 q ha hb
    | true =>
      simp only [d10826, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27033 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d108840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d108840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52197, d108840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10845 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27053 q ha hb
    | true =>
      simp only [d10845, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10846 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10846, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74106 q = 1) (hb : d108841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74106, d108841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74106, d108841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74107 q = 1) (hb : d108842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74107, d108842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74107, d108842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74108 q = 1) (hb : d108843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74108, d108843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74108, d108843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74109 q = 1) (hb : d108844 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74109, d108844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74109, d108844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27055 (p : Pattern) (ha : d74115 p = 1) (hb : d108850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27036 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27036 q ha hb
    | true =>
      simp only [d10727, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27037 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74088 q = 1) (hb : d108828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74088, d108828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27044 q ha hb
    | true =>
      simp only [d74088, d108828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27049 q ha hb
  have h7 (q : Pattern) (ha : d10802 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27038 q ha hb
    | true =>
      simp only [d10802, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d74089 q = 1) (hb : d108829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74089, d108829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74089, d108829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74090 q = 1) (hb : d108830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74090, d108830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74090, d108830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74091 q = 1) (hb : d108831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74091, d108831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74091, d108831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74095 q = 1) (hb : d108835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74095, d108835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74095, d108835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27050 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d74096 q = 1) (hb : d108836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74096, d108836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74096, d108836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74097 q = 1) (hb : d108837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74097, d108837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74097, d108837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74098 q = 1) (hb : d108838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74098, d108838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74098, d108838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74099 q = 1) (hb : d108839 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74099, d108839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74099, d108839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74110 q = 1) (hb : d108845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74110, d108845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74110, d108845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27054 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d74111 q = 1) (hb : d108846 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74111, d108846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74111, d108846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74112 q = 1) (hb : d108847 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74112, d108847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74112, d108847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74113 q = 1) (hb : d108848 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74113, d108848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74113, d108848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74114 q = 1) (hb : d108849 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74114, d108849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74114, d108849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74115 q = 1) (hb : d108850 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74115, d108850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74115, d108850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27056 (p : Pattern) (ha : d74121 p = 1) (hb : d108856 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d108813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27035 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d108814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d108815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d108816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d108817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74116 q = 1) (hb : d108851 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74116, d108851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74116, d108851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27055 q ha hb
  have h11 (q : Pattern) (ha : d74117 q = 1) (hb : d108852 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74117, d108852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74117, d108852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74118 q = 1) (hb : d108853 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74118, d108853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74118, d108853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74119 q = 1) (hb : d108854 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74119, d108854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74119, d108854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74120 q = 1) (hb : d108855 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74120, d108855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74120, d108855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74121 q = 1) (hb : d108856 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74121, d108856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74121, d108856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro27057 (p : Pattern) (ha : d10865 p = 1) (hb : d52224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10745 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10863 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10864 q = 1) (hb : d52223 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d52223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10864, d52223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10865 q = 1) (hb : d52224 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d52224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10865, d52224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27058 (p : Pattern) (ha : d10875 p = 1) (hb : d52234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10875 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d52234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d52234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27059 (p : Pattern) (ha : d10885 p = 1) (hb : d52244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
    | true =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10885 q = 1) (hb : d52244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d52244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d52244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27060 (p : Pattern) (ha : d10888 p = 1) (hb : d52247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10888 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d52247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10888, d52247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27061 (p : Pattern) (ha : d10895 p = 1) (hb : d52254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
    | true =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10890 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27060 q ha hb
    | true =>
      simp only [d10890, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q ha hb
  have h7 (q : Pattern) (ha : d10891 q = 1) (hb : d52250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d52250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d52250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10892 q = 1) (hb : d52251 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d52251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10892, d52251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10893 q = 1) (hb : d52252 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d52252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d52252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10894 q = 1) (hb : d52253 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d52253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d52253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10895 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10895, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27062 (p : Pattern) (ha : d10992 p = 1) (hb : d52342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
    | true =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
    | true =>
      simp only [d10987, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10992 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d52342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10992, d52342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27063 (p : Pattern) (ha : d10900 p = 1) (hb : d52259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10900 q = 1) (hb : d52259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d52259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d52259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27064 (p : Pattern) (ha : d10909 p = 1) (hb : d52268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d52266 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10909 q = 1) (hb : d52268 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d52268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d52268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27065 (p : Pattern) (ha : d10921 p = 1) (hb : d52301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10916 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d10916, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10917 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10918 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10919 q = 1) (hb : d52299 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10919, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10745 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10920 q = 1) (hb : d52300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d52300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10920, d52300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10921 q = 1) (hb : d52301 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d52301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10921, d52301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27066 (p : Pattern) (ha : d10927 p = 1) (hb : d52307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27065 q ha hb
    | true =>
      simp only [d10922, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d52304 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d52305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d52307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d52307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d52307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27067 (p : Pattern) (ha : d10955 p = 1) (hb : d74125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d74123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d74124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d74125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d74125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d74125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27068 (p : Pattern) (ha : d74131 p = 1) (hb : d108861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27063 q ha hb
    | true =>
      simp only [d10903, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24932 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27064 q ha hb
    | true =>
      simp only [d10913, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24933 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27066 q ha hb
    | true =>
      simp only [d10928, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52309 q = 1) (hb : d108857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52309, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10956 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27067 q ha hb
    | true =>
      simp only [d10956, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10957 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10957, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74128 q = 1) (hb : d108858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74128, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74128, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74129 q = 1) (hb : d108859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74129, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74129, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74130 q = 1) (hb : d108860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74130, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74130, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74131 q = 1) (hb : d108861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74131, d108861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74131, d108861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27069 (p : Pattern) (ha : d10962 p = 1) (hb : d52316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10962 q = 1) (hb : d52316 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d52316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10962, d52316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27070 (p : Pattern) (ha : d10968 p = 1) (hb : d52322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d52266 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10968 q = 1) (hb : d52322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d52322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10968, d52322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27071 (p : Pattern) (ha : d10973 p = 1) (hb : d52327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27065 q ha hb
    | true =>
      simp only [d10922, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d52304 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d52305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d52327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d52327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d52327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27072 (p : Pattern) (ha : d10979 p = 1) (hb : d74132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27057 q ha hb
    | true =>
      simp only [d10866, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d74123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d74124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d74132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d74132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d74132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27073 (p : Pattern) (ha : d74138 p = 1) (hb : d108866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27063 q ha hb
    | true =>
      simp only [d10903, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24932 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27064 q ha hb
    | true =>
      simp only [d10913, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24933 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27066 q ha hb
    | true =>
      simp only [d10928, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52309 q = 1) (hb : d108857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52309, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10956 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27067 q ha hb
    | true =>
      simp only [d10956, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10957 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10957, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74128 q = 1) (hb : d108858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74128, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74128, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74129 q = 1) (hb : d108859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74129, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74129, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74130 q = 1) (hb : d108860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74130, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74130, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10964 q = 1) (hb : d52318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d52318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27069 q ha hb
    | true =>
      simp only [d10964, d52318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24940 q ha hb
  have h17 (q : Pattern) (ha : d10965 q = 1) (hb : d52319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d52319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d52319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10966 q = 1) (hb : d52320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d52320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10966, d52320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10967 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d52321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d52321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10970 q = 1) (hb : d52324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27070 q ha hb
    | true =>
      simp only [d10970, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24941 q ha hb
  have h21 (q : Pattern) (ha : d10971 q = 1) (hb : d52325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10972 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10972, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d10974 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27071 q ha hb
    | true =>
      simp only [d10974, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27060 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52329 q = 1) (hb : d108862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52329, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10980 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27072 q ha hb
    | true =>
      simp only [d10980, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10981 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10981, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74135 q = 1) (hb : d108863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74135, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74135, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74136 q = 1) (hb : d108864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74136, d108864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74136, d108864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74137 q = 1) (hb : d108865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74137, d108865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74137, d108865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74138 q = 1) (hb : d108866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74138, d108866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74138, d108866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27074 (p : Pattern) (ha : d74145 p = 1) (hb : d108873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27071 q ha hb
    | true =>
      simp only [d10974, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27060 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52329 q = 1) (hb : d108862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52329, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10980 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27072 q ha hb
    | true =>
      simp only [d10980, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10981 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10981, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74135 q = 1) (hb : d108863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74135, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74135, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74143 q = 1) (hb : d108871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74143, d108871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74143, d108871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74144 q = 1) (hb : d108872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74144, d108872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74144, d108872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74145 q = 1) (hb : d108873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74145, d108873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74145, d108873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27075 (p : Pattern) (ha : d11018 p = 1) (hb : d52374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11013 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d11013, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11014 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11015 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10814 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10815 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10816 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11016 q = 1) (hb : d52372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11016, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10817 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11017 q = 1) (hb : d52373 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d52373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11017, d52373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11018 q = 1) (hb : d52374 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d52374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11018, d52374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27076 (p : Pattern) (ha : d11023 p = 1) (hb : d52379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10817 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11021 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11022 q = 1) (hb : d52378 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d52378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11022, d52378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11023 q = 1) (hb : d52379 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d52379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11023, d52379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27077 (p : Pattern) (ha : d11029 p = 1) (hb : d52385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d52375 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d52375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27075 q ha hb
    | true =>
      simp only [d11019, d52375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d52376 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d52376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d52376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27076 q ha hb
    | true =>
      simp only [d11024, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d52382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d52382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d52382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d52383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d52383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d52383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d52384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d52384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d52384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d52385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d52385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d52385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27078 (p : Pattern) (ha : d11037 p = 1) (hb : d52393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27076 q ha hb
    | true =>
      simp only [d11024, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24925 q ha hb
    | true =>
      simp only [d11032, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11034 q = 1) (hb : d52390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11035 q = 1) (hb : d52391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11035, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11036 q = 1) (hb : d52392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11036, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11037 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11037, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27079 (p : Pattern) (ha : d11065 p = 1) (hb : d74154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27076 q ha hb
    | true =>
      simp only [d11024, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d74151 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d74151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d74151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d74152 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d74152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d74152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d74153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d74153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d74153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d74154 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d74154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d74154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27080 (p : Pattern) (ha : d74160 p = 1) (hb : d108883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27077 q ha hb
    | true =>
      simp only [d11038, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27078 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52400 q = 1) (hb : d108879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d108879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52400, d108879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11066 q = 1) (hb : d74155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27079 q ha hb
    | true =>
      simp only [d11066, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11067 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11067, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74157 q = 1) (hb : d108880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74157, d108880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74157, d108880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74158 q = 1) (hb : d108881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74158, d108881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74158, d108881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74159 q = 1) (hb : d108882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74159, d108882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74159, d108882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74160 q = 1) (hb : d108883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74160, d108883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74160, d108883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27081 (p : Pattern) (ha : d74166 p = 1) (hb : d108889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27059 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27059 q ha hb
    | true =>
      simp only [d10896, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27061 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74139 q = 1) (hb : d108867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74139, d108867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27068 q ha hb
    | true =>
      simp only [d74139, d108867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27073 q ha hb
  have h7 (q : Pattern) (ha : d10999 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27062 q ha hb
    | true =>
      simp only [d10999, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24923 q ha hb
  have h8 (q : Pattern) (ha : d74140 q = 1) (hb : d108868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74140, d108868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74140, d108868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74141 q = 1) (hb : d108869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74141, d108869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74141, d108869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74142 q = 1) (hb : d108870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74142, d108870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74142, d108870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74146 q = 1) (hb : d108874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74146, d108874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74146, d108874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27074 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24924 q ha hb
  have h13 (q : Pattern) (ha : d74147 q = 1) (hb : d108875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74147, d108875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74147, d108875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74148 q = 1) (hb : d108876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74148, d108876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74148, d108876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74149 q = 1) (hb : d108877 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74149, d108877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74149, d108877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74150 q = 1) (hb : d108878 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74150, d108878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74150, d108878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74161 q = 1) (hb : d108884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74161, d108884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74161, d108884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27080 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24927 q ha hb
  have h19 (q : Pattern) (ha : d74162 q = 1) (hb : d108885 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74162, d108885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74162, d108885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74163 q = 1) (hb : d108886 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74163, d108886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74163, d108886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74164 q = 1) (hb : d108887 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74164, d108887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74164, d108887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74165 q = 1) (hb : d108888 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74165, d108888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74165, d108888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74166 q = 1) (hb : d108889 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74166, d108889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74166, d108889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27082 (p : Pattern) (ha : d74172 p = 1) (hb : d108895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74167 q = 1) (hb : d108890 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74167, d108890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74167, d108890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27081 q ha hb
  have h2 (q : Pattern) (ha : d74168 q = 1) (hb : d108891 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74168, d108891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74168, d108891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74169 q = 1) (hb : d108892 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74169, d108892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74169, d108892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74170 q = 1) (hb : d108893 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74170, d108893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74170, d108893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74171 q = 1) (hb : d108894 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74171, d108894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74171, d108894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74172 q = 1) (hb : d108895 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74172, d108895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74172, d108895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27083 (p : Pattern) (ha : d11105 p = 1) (hb : d52446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11102 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11103 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11103, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11104 q = 1) (hb : d52445 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d52445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11104, d52445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11105 q = 1) (hb : d52446 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d52446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11105, d52446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27084 (p : Pattern) (ha : d11115 p = 1) (hb : d52456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11115 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d52456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d52456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27085 (p : Pattern) (ha : d11125 p = 1) (hb : d52466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
    | true =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11125 q = 1) (hb : d52466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d52466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d52466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27086 (p : Pattern) (ha : d11128 p = 1) (hb : d52469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11128 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d52469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11128, d52469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27087 (p : Pattern) (ha : d11135 p = 1) (hb : d52476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
    | true =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11130 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27086 q ha hb
    | true =>
      simp only [d11130, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q ha hb
  have h7 (q : Pattern) (ha : d11131 q = 1) (hb : d52472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d52472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d52472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11132 q = 1) (hb : d52473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d52473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11132, d52473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11133 q = 1) (hb : d52474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d52474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d52474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11134 q = 1) (hb : d52475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d52475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d52475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11135 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11135, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27088 (p : Pattern) (ha : d11243 p = 1) (hb : d52563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
    | true =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
    | true =>
      simp only [d11238, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11243 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d52563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11243, d52563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27089 (p : Pattern) (ha : d11140 p = 1) (hb : d52481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11140 q = 1) (hb : d52481 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d52481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d52481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27090 (p : Pattern) (ha : d11149 p = 1) (hb : d52490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d52488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11149 q = 1) (hb : d52490 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d52490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d52490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27091 (p : Pattern) (ha : d11161 p = 1) (hb : d52522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52433 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11156 q = 1) (hb : d52517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d11156, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11157 q = 1) (hb : d52518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11158 q = 1) (hb : d52519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11096 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11097 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11098 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11159 q = 1) (hb : d52520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d52520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11159, d52520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11102 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11160 q = 1) (hb : d52521 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d52521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11160, d52521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11161 q = 1) (hb : d52522 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d52522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11161, d52522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27092 (p : Pattern) (ha : d11167 p = 1) (hb : d52528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27091 q ha hb
    | true =>
      simp only [d11162, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d52525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d52526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d52528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d52528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d52528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27093 (p : Pattern) (ha : d11200 p = 1) (hb : d74189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11102 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74183 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11195 q = 1) (hb : d74184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d74184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9260 q ha hb
    | true =>
      simp only [d11195, d74184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11196 q = 1) (hb : d74185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d74185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11196, d74185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11197 q = 1) (hb : d74186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d74186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11197, d74186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11198 q = 1) (hb : d74187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d74187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11198, d74187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d11199 q = 1) (hb : d74188 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d74188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11199, d74188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11200 q = 1) (hb : d74189 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d74189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11200, d74189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27094 (p : Pattern) (ha : d11206 p = 1) (hb : d74195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d74190 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d74190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27093 q ha hb
    | true =>
      simp only [d11201, d74190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d74191 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d74191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d74191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d74192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d74192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d74192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d74193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d74193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d74193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d74194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d74194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d74194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d74195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d74195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d74195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27095 (p : Pattern) (ha : d74201 p = 1) (hb : d108901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27089 q ha hb
    | true =>
      simp only [d11143, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24969 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27090 q ha hb
    | true =>
      simp only [d11153, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24970 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27092 q ha hb
    | true =>
      simp only [d11168, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52530 q = 1) (hb : d108897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52530, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52530, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11207 q = 1) (hb : d74196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27094 q ha hb
    | true =>
      simp only [d11207, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11208 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11208, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74198 q = 1) (hb : d108898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74198, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74198, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74199 q = 1) (hb : d108899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74199, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74199, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74200 q = 1) (hb : d108900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74200, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74200, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74201 q = 1) (hb : d108901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74201, d108901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74201, d108901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27096 (p : Pattern) (ha : d11213 p = 1) (hb : d52537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11213 q = 1) (hb : d52537 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d52537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11213, d52537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27097 (p : Pattern) (ha : d11219 p = 1) (hb : d52543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d52488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11219 q = 1) (hb : d52543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d52543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11219, d52543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27098 (p : Pattern) (ha : d11224 p = 1) (hb : d52548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27091 q ha hb
    | true =>
      simp only [d11162, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27083 q ha hb
    | true =>
      simp only [d11106, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d52525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d52526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d52548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d52548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d52548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27099 (p : Pattern) (ha : d11230 p = 1) (hb : d74202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d74190 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d74190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27093 q ha hb
    | true =>
      simp only [d11201, d74190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d74191 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d74191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d74191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d74192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d74192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d74192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d74193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d74193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d74193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d74194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d74194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d74194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11230 q = 1) (hb : d74202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d74202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11230, d74202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27100 (p : Pattern) (ha : d74208 p = 1) (hb : d108906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27089 q ha hb
    | true =>
      simp only [d11143, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24969 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27090 q ha hb
    | true =>
      simp only [d11153, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24970 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27092 q ha hb
    | true =>
      simp only [d11168, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52530 q = 1) (hb : d108897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52530, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52530, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11207 q = 1) (hb : d74196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27094 q ha hb
    | true =>
      simp only [d11207, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11208 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11208, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74198 q = 1) (hb : d108898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74198, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74198, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74199 q = 1) (hb : d108899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74199, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74199, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74200 q = 1) (hb : d108900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74200, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74200, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11215 q = 1) (hb : d52539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27096 q ha hb
    | true =>
      simp only [d11215, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24977 q ha hb
  have h17 (q : Pattern) (ha : d11216 q = 1) (hb : d52540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11217 q = 1) (hb : d52541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d11217, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d11218 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11221 q = 1) (hb : d52545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27097 q ha hb
    | true =>
      simp only [d11221, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24978 q ha hb
  have h21 (q : Pattern) (ha : d11222 q = 1) (hb : d52546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11223 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d11223, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d11225 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27098 q ha hb
    | true =>
      simp only [d11225, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27086 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52550 q = 1) (hb : d108902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52550, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d11231 q = 1) (hb : d74203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27099 q ha hb
    | true =>
      simp only [d11231, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d11232 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d11232, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74205 q = 1) (hb : d108903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74205, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74205, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74206 q = 1) (hb : d108904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74206, d108904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74206, d108904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74207 q = 1) (hb : d108905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74207, d108905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74207, d108905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74208 q = 1) (hb : d108906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74208, d108906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74208, d108906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27101 (p : Pattern) (ha : d74215 p = 1) (hb : d108913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27098 q ha hb
    | true =>
      simp only [d11225, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27086 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52550 q = 1) (hb : d108902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52550, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11231 q = 1) (hb : d74203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27099 q ha hb
    | true =>
      simp only [d11231, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11232 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11232, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74205 q = 1) (hb : d108903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74205, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74205, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74213 q = 1) (hb : d108911 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74213, d108911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74213, d108911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74214 q = 1) (hb : d108912 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74214, d108912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74214, d108912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74215 q = 1) (hb : d108913 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74215, d108913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74215, d108913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27102 (p : Pattern) (ha : d11276 p = 1) (hb : d52611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11264 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d11264, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11265 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11265, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11266 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11266, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11267 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11268 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11269 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11270 q = 1) (hb : d52604 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11270, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11274 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11275 q = 1) (hb : d52610 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d52610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11275, d52610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11276 q = 1) (hb : d52611 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d52611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11276, d52611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27103 (p : Pattern) (ha : d11281 p = 1) (hb : d52616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11274 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11279 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11279, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11280 q = 1) (hb : d52615 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d52615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11280, d52615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11281 q = 1) (hb : d52616 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d52616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11281, d52616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27104 (p : Pattern) (ha : d11287 p = 1) (hb : d52622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d52612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27102 q ha hb
    | true =>
      simp only [d11277, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d52613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11282 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27103 q ha hb
    | true =>
      simp only [d11282, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11283 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11284 q = 1) (hb : d52619 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d52619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d52619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d52620 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d52620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11285, d52620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d52621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d52621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d52621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d52622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d52622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d52622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27105 (p : Pattern) (ha : d11295 p = 1) (hb : d52630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27103 q ha hb
    | true =>
      simp only [d11282, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11290 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24961 q ha hb
    | true =>
      simp only [d11290, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11291 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11292 q = 1) (hb : d52627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d52627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d52627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11293 q = 1) (hb : d52628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d52628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11293, d52628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11294 q = 1) (hb : d52629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d52629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11294, d52629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11295 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d52630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11295, d52630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27106 (p : Pattern) (ha : d11328 p = 1) (hb : d74233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11274 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74227 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11323 q = 1) (hb : d74228 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11323, d74228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9268 q ha hb
    | true =>
      simp only [d11323, d74228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11324 q = 1) (hb : d74229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11324, d74229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11324, d74229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11325 q = 1) (hb : d74230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11325, d74230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11325, d74230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11326 q = 1) (hb : d74231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11326, d74231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11326, d74231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d11327 q = 1) (hb : d74232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d74232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11327, d74232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11328 q = 1) (hb : d74233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d74233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11328, d74233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27107 (p : Pattern) (ha : d11334 p = 1) (hb : d74239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d74234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d74234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27106 q ha hb
    | true =>
      simp only [d11329, d74234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d74235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d74235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d74235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11331 q = 1) (hb : d74236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d74236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d74236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11332 q = 1) (hb : d74237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d74237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11332, d74237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11333 q = 1) (hb : d74238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d74238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11333, d74238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11334 q = 1) (hb : d74239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d74239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11334, d74239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27108 (p : Pattern) (ha : d74245 p = 1) (hb : d108923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27104 q ha hb
    | true =>
      simp only [d11296, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27105 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52637 q = 1) (hb : d108919 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d108919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52637, d108919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11335 q = 1) (hb : d74240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d74240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27107 q ha hb
    | true =>
      simp only [d11335, d74240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11336 q = 1) (hb : d74241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d74241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11336, d74241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74242 q = 1) (hb : d108920 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74242, d108920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74242, d108920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74243 q = 1) (hb : d108921 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74243, d108921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74243, d108921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74244 q = 1) (hb : d108922 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74244, d108922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74244, d108922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74245 q = 1) (hb : d108923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74245, d108923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74245, d108923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27109 (p : Pattern) (ha : d74251 p = 1) (hb : d108929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27085 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27085 q ha hb
    | true =>
      simp only [d11136, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27087 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74209 q = 1) (hb : d108907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74209, d108907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27095 q ha hb
    | true =>
      simp only [d74209, d108907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27100 q ha hb
  have h7 (q : Pattern) (ha : d11250 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27088 q ha hb
    | true =>
      simp only [d11250, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24959 q ha hb
  have h8 (q : Pattern) (ha : d74210 q = 1) (hb : d108908 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74210, d108908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74210, d108908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74211 q = 1) (hb : d108909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74211, d108909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74211, d108909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74212 q = 1) (hb : d108910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74212, d108910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74212, d108910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74216 q = 1) (hb : d108914 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74216, d108914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74216, d108914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27101 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24960 q ha hb
  have h13 (q : Pattern) (ha : d74217 q = 1) (hb : d108915 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74217, d108915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74217, d108915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74218 q = 1) (hb : d108916 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74218, d108916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74218, d108916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74219 q = 1) (hb : d108917 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74219, d108917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74219, d108917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74220 q = 1) (hb : d108918 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74220, d108918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74220, d108918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74246 q = 1) (hb : d108924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74246, d108924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74246, d108924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27108 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24963 q ha hb
  have h19 (q : Pattern) (ha : d74247 q = 1) (hb : d108925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74247, d108925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74247, d108925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74248 q = 1) (hb : d108926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74248, d108926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74248, d108926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74249 q = 1) (hb : d108927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74249, d108927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74249, d108927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74250 q = 1) (hb : d108928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74250, d108928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74250, d108928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74251 q = 1) (hb : d108929 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74251, d108929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74251, d108929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27110 (p : Pattern) (ha : d74257 p = 1) (hb : d108935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74252 q = 1) (hb : d108930 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74252, d108930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74252, d108930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27109 q ha hb
  have h2 (q : Pattern) (ha : d74253 q = 1) (hb : d108931 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74253, d108931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74253, d108931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74254 q = 1) (hb : d108932 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74254, d108932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74254, d108932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74255 q = 1) (hb : d108933 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74255, d108933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74255, d108933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74256 q = 1) (hb : d108934 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74256, d108934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74256, d108934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74257 q = 1) (hb : d108935 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74257, d108935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74257, d108935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27111 (p : Pattern) (ha : d11375 p = 1) (hb : d52729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11372 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11373 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11373, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11374 q = 1) (hb : d52728 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d52728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11374, d52728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11375 q = 1) (hb : d52729 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d52729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11375, d52729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27112 (p : Pattern) (ha : d11385 p = 1) (hb : d52739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11385 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d52739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d52739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27113 (p : Pattern) (ha : d11395 p = 1) (hb : d52749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
    | true =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11395 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27114 (p : Pattern) (ha : d11398 p = 1) (hb : d52752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11398 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d52752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11398, d52752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27115 (p : Pattern) (ha : d11405 p = 1) (hb : d52759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
    | true =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11400 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27114 q ha hb
    | true =>
      simp only [d11400, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q ha hb
  have h7 (q : Pattern) (ha : d11401 q = 1) (hb : d52755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11402 q = 1) (hb : d52756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11402, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11403 q = 1) (hb : d52757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11404 q = 1) (hb : d52758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11405 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11405, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27116 (p : Pattern) (ha : d11513 p = 1) (hb : d52843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
    | true =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
    | true =>
      simp only [d11508, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11513 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d52843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11513, d52843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27117 (p : Pattern) (ha : d11410 p = 1) (hb : d52764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11410 q = 1) (hb : d52764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d52764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d52764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27118 (p : Pattern) (ha : d11419 p = 1) (hb : d52773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11419 q = 1) (hb : d52773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d52773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d52773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27119 (p : Pattern) (ha : d11431 p = 1) (hb : d52802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52707 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11426 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d11426, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11427 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11427, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11428 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11428, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11366 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11367 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11368 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11429 q = 1) (hb : d52800 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11429, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11372 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11430 q = 1) (hb : d52801 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d52801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11430, d52801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11431 q = 1) (hb : d52802 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d52802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11431, d52802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27120 (p : Pattern) (ha : d11437 p = 1) (hb : d52808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27119 q ha hb
    | true =>
      simp only [d11432, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d52805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d52806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d52808 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d52808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d52808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27121 (p : Pattern) (ha : d11470 p = 1) (hb : d74278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11372 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74272 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11465 q = 1) (hb : d74273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11465, d74273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9276 q ha hb
    | true =>
      simp only [d11465, d74273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11466 q = 1) (hb : d74274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11466, d74274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11466, d74274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11467 q = 1) (hb : d74275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11467, d74275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11467, d74275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11468 q = 1) (hb : d74276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11468, d74276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11468, d74276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d11469 q = 1) (hb : d74277 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d74277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11469, d74277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11470 q = 1) (hb : d74278 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d74278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11470, d74278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27122 (p : Pattern) (ha : d11476 p = 1) (hb : d74284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d74279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d74279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27121 q ha hb
    | true =>
      simp only [d11471, d74279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d74280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d74280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d74280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d74281 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d74281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d74281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d74282 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d74282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d74282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d74283 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d74283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d74283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11476 q = 1) (hb : d74284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d74284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d74284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27123 (p : Pattern) (ha : d74290 p = 1) (hb : d108942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27117 q ha hb
    | true =>
      simp only [d11413, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25007 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27118 q ha hb
    | true =>
      simp only [d11423, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25008 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27120 q ha hb
    | true =>
      simp only [d11438, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52810 q = 1) (hb : d108938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52810, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11477 q = 1) (hb : d74285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27122 q ha hb
    | true =>
      simp only [d11477, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11478 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11478, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74287 q = 1) (hb : d108939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74287, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74288 q = 1) (hb : d108940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74288, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74289 q = 1) (hb : d108941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74289, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74290 q = 1) (hb : d108942 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74290, d108942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74290, d108942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27124 (p : Pattern) (ha : d11483 p = 1) (hb : d52817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11483 q = 1) (hb : d52817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d52817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11483, d52817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27125 (p : Pattern) (ha : d11489 p = 1) (hb : d52823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11489 q = 1) (hb : d52823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d52823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11489, d52823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27126 (p : Pattern) (ha : d11494 p = 1) (hb : d52828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27119 q ha hb
    | true =>
      simp only [d11432, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27111 q ha hb
    | true =>
      simp only [d11376, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d52805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d52806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d52828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d52828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d52828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27127 (p : Pattern) (ha : d11500 p = 1) (hb : d74291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d74279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d74279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27121 q ha hb
    | true =>
      simp only [d11471, d74279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d74280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d74280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d74280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d74281 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d74281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d74281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d74282 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d74282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d74282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d74283 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d74283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d74283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11500 q = 1) (hb : d74291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d74291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11500, d74291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27128 (p : Pattern) (ha : d74297 p = 1) (hb : d108947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27117 q ha hb
    | true =>
      simp only [d11413, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25007 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27118 q ha hb
    | true =>
      simp only [d11423, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25008 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27120 q ha hb
    | true =>
      simp only [d11438, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52810 q = 1) (hb : d108938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52810, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11477 q = 1) (hb : d74285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27122 q ha hb
    | true =>
      simp only [d11477, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11478 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11478, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74287 q = 1) (hb : d108939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74287, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74288 q = 1) (hb : d108940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74288, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74289 q = 1) (hb : d108941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74289, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11485 q = 1) (hb : d52819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27124 q ha hb
    | true =>
      simp only [d11485, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25015 q ha hb
  have h17 (q : Pattern) (ha : d11486 q = 1) (hb : d52820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11487 q = 1) (hb : d52821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d11487, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d11488 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11491 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27125 q ha hb
    | true =>
      simp only [d11491, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25016 q ha hb
  have h21 (q : Pattern) (ha : d11492 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11493 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d11493, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d11495 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27126 q ha hb
    | true =>
      simp only [d11495, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27114 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52830 q = 1) (hb : d108943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52830, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d11501 q = 1) (hb : d74292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27127 q ha hb
    | true =>
      simp only [d11501, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d11502 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d11502, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74294 q = 1) (hb : d108944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74294, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74295 q = 1) (hb : d108945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74295, d108945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74295, d108945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74296 q = 1) (hb : d108946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74296, d108946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74296, d108946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74297 q = 1) (hb : d108947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74297, d108947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74297, d108947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27129 (p : Pattern) (ha : d74304 p = 1) (hb : d108954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27126 q ha hb
    | true =>
      simp only [d11495, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27114 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52830 q = 1) (hb : d108943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52830, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11501 q = 1) (hb : d74292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27127 q ha hb
    | true =>
      simp only [d11501, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11502 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11502, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74294 q = 1) (hb : d108944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74294, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74302 q = 1) (hb : d108952 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74302, d108952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74302, d108952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74303 q = 1) (hb : d108953 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74303, d108953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74303, d108953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74304 q = 1) (hb : d108954 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d108954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d108954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27130 (p : Pattern) (ha : d11546 p = 1) (hb : d52905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11534 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d11534, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11535 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11535, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11536 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11536, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11537 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11538 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11539 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11540 q = 1) (hb : d52893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11540, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11544 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11545 q = 1) (hb : d52904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d52904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11545, d52904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11546 q = 1) (hb : d52905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d52905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11546, d52905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27131 (p : Pattern) (ha : d11551 p = 1) (hb : d52910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11544 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11549 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11549, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11550 q = 1) (hb : d52909 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d52909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11550, d52909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11551 q = 1) (hb : d52910 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d52910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11551, d52910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27132 (p : Pattern) (ha : d11557 p = 1) (hb : d52916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d52906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27130 q ha hb
    | true =>
      simp only [d11547, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d52907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11552 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27131 q ha hb
    | true =>
      simp only [d11552, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11553 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11554 q = 1) (hb : d52913 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d52913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d52913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d52914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d52914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11555, d52914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d52915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d52915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d52915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d52916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d52916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d52916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27133 (p : Pattern) (ha : d11565 p = 1) (hb : d52924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27131 q ha hb
    | true =>
      simp only [d11552, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11560 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24999 q ha hb
    | true =>
      simp only [d11560, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11561 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11562 q = 1) (hb : d52921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d52921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d52921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11563 q = 1) (hb : d52922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d52922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11563, d52922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11564 q = 1) (hb : d52923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d52923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11564, d52923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11565 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d52924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11565, d52924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27134 (p : Pattern) (ha : d11598 p = 1) (hb : d74322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11544 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74316 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11593 q = 1) (hb : d74317 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11593, d74317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9284 q ha hb
    | true =>
      simp only [d11593, d74317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11594 q = 1) (hb : d74318 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11594, d74318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11594, d74318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11595 q = 1) (hb : d74319 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11595, d74319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11595, d74319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11596 q = 1) (hb : d74320 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11596, d74320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11596, d74320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d11597 q = 1) (hb : d74321 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d74321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11597, d74321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11598 q = 1) (hb : d74322 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d74322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11598, d74322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27135 (p : Pattern) (ha : d11604 p = 1) (hb : d74328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d74323 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d74323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27134 q ha hb
    | true =>
      simp only [d11599, d74323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d74324 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d74324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d74324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11601 q = 1) (hb : d74325 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d74325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d74325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11602 q = 1) (hb : d74326 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d74326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11602, d74326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11603 q = 1) (hb : d74327 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d74327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11603, d74327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11604 q = 1) (hb : d74328 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d74328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11604, d74328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27136 (p : Pattern) (ha : d74334 p = 1) (hb : d108964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27132 q ha hb
    | true =>
      simp only [d11566, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27133 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d108960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d108960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d108960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11605 q = 1) (hb : d74329 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d74329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27135 q ha hb
    | true =>
      simp only [d11605, d74329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11606 q = 1) (hb : d74330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d74330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11606, d74330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74331 q = 1) (hb : d108961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d108961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d108961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74332 q = 1) (hb : d108962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d108962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d108962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74333 q = 1) (hb : d108963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d108963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d108963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74334 q = 1) (hb : d108964 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d108964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d108964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27137 (p : Pattern) (ha : d74340 p = 1) (hb : d108970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27113 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27113 q ha hb
    | true =>
      simp only [d11406, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27115 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74298 q = 1) (hb : d108948 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74298, d108948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27123 q ha hb
    | true =>
      simp only [d74298, d108948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27128 q ha hb
  have h7 (q : Pattern) (ha : d11520 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27116 q ha hb
    | true =>
      simp only [d11520, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24997 q ha hb
  have h8 (q : Pattern) (ha : d74299 q = 1) (hb : d108949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74299, d108949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74299, d108949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74300 q = 1) (hb : d108950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d108950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74300, d108950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74301 q = 1) (hb : d108951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d108951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74301, d108951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74305 q = 1) (hb : d108955 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d108955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74305, d108955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27129 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24998 q ha hb
  have h13 (q : Pattern) (ha : d74306 q = 1) (hb : d108956 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d108956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74306, d108956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74307 q = 1) (hb : d108957 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d108957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74307, d108957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74308 q = 1) (hb : d108958 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d108958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74308, d108958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74309 q = 1) (hb : d108959 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d108959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74309, d108959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74335 q = 1) (hb : d108965 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d108965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74335, d108965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27136 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25001 q ha hb
  have h19 (q : Pattern) (ha : d74336 q = 1) (hb : d108966 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d108966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74336, d108966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74337 q = 1) (hb : d108967 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d108967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74337, d108967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74338 q = 1) (hb : d108968 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d108968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74338, d108968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74339 q = 1) (hb : d108969 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d108969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74339, d108969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74340 q = 1) (hb : d108970 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d108970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74340, d108970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27138 (p : Pattern) (ha : d74346 p = 1) (hb : d108976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d108971 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d108971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d108971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27137 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d108972 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d108972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d108972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d108973 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d108973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d108973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d108974 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d108974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d108974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d108975 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d108975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d108975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d108976 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d108976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d108976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27139 (p : Pattern) (ha : d11646 p = 1) (hb : d53050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11643 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11644 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11644, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11645 q = 1) (hb : d53049 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d53049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11645, d53049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11646 q = 1) (hb : d53050 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d53050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11646, d53050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27140 (p : Pattern) (ha : d11656 p = 1) (hb : d53060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11656 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d53060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d53060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27141 (p : Pattern) (ha : d11666 p = 1) (hb : d53070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
    | true =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11666 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27142 (p : Pattern) (ha : d11669 p = 1) (hb : d53073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11669 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d53073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11669, d53073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27143 (p : Pattern) (ha : d11676 p = 1) (hb : d53080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
    | true =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11671 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27142 q ha hb
    | true =>
      simp only [d11671, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q ha hb
  have h7 (q : Pattern) (ha : d11672 q = 1) (hb : d53076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11673 q = 1) (hb : d53077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11673, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11674 q = 1) (hb : d53078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11675 q = 1) (hb : d53079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11676 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11676, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27144 (p : Pattern) (ha : d11784 p = 1) (hb : d53158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
    | true =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
    | true =>
      simp only [d11779, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11784 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d53158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11784, d53158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27145 (p : Pattern) (ha : d11681 p = 1) (hb : d53085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11681 q = 1) (hb : d53085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d53085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d53085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27146 (p : Pattern) (ha : d11690 p = 1) (hb : d53094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11690 q = 1) (hb : d53094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d53094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d53094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27147 (p : Pattern) (ha : d11702 p = 1) (hb : d53117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11697 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d11697, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11698 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11698, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11699 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11699, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11637 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11638 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11639 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11700 q = 1) (hb : d53115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11700, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11643 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11701 q = 1) (hb : d53116 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d53116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11701, d53116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11702 q = 1) (hb : d53117 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d53117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11702, d53117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27148 (p : Pattern) (ha : d11708 p = 1) (hb : d53123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27147 q ha hb
    | true =>
      simp only [d11703, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d53120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d53121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d53123 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d53123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d53123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27149 (p : Pattern) (ha : d11741 p = 1) (hb : d74368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11643 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74362 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11736 q = 1) (hb : d74363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11736, d74363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9292 q ha hb
    | true =>
      simp only [d11736, d74363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11737 q = 1) (hb : d74364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11737, d74364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11737, d74364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11738 q = 1) (hb : d74365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11738, d74365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11738, d74365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11739 q = 1) (hb : d74366 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11739, d74366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11739, d74366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d11740 q = 1) (hb : d74367 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d74367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11740, d74367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11741 q = 1) (hb : d74368 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d74368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11741, d74368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27150 (p : Pattern) (ha : d11747 p = 1) (hb : d74374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d74369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d74369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27149 q ha hb
    | true =>
      simp only [d11742, d74369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d74370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d74370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d74370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d74371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d74371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d74371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d74372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d74372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d74372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d74373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d74373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d74373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11747 q = 1) (hb : d74374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d74374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d74374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27151 (p : Pattern) (ha : d74380 p = 1) (hb : d108984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27145 q ha hb
    | true =>
      simp only [d11684, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25045 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27146 q ha hb
    | true =>
      simp only [d11694, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25046 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27148 q ha hb
    | true =>
      simp only [d11709, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53125 q = 1) (hb : d108980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53125, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11748 q = 1) (hb : d74375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27150 q ha hb
    | true =>
      simp only [d11748, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11749 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11749, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74377 q = 1) (hb : d108981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74377, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74378 q = 1) (hb : d108982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74378, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74379 q = 1) (hb : d108983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74379, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74380 q = 1) (hb : d108984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74380, d108984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74380, d108984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27152 (p : Pattern) (ha : d11754 p = 1) (hb : d53132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11754 q = 1) (hb : d53132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d53132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11754, d53132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27153 (p : Pattern) (ha : d11760 p = 1) (hb : d53138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11760 q = 1) (hb : d53138 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d53138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11760, d53138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27154 (p : Pattern) (ha : d11765 p = 1) (hb : d53143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27147 q ha hb
    | true =>
      simp only [d11703, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27139 q ha hb
    | true =>
      simp only [d11647, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d53120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d53121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d53143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d53143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d53143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27155 (p : Pattern) (ha : d11771 p = 1) (hb : d74381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d74369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d74369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27149 q ha hb
    | true =>
      simp only [d11742, d74369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d74370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d74370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d74370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d74371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d74371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d74371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d74372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d74372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d74372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d74373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d74373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d74373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11771 q = 1) (hb : d74381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d74381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11771, d74381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27156 (p : Pattern) (ha : d74387 p = 1) (hb : d108989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27145 q ha hb
    | true =>
      simp only [d11684, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25045 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27146 q ha hb
    | true =>
      simp only [d11694, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25046 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27148 q ha hb
    | true =>
      simp only [d11709, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53125 q = 1) (hb : d108980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53125, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11748 q = 1) (hb : d74375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27150 q ha hb
    | true =>
      simp only [d11748, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11749 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11749, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74377 q = 1) (hb : d108981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74377, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74378 q = 1) (hb : d108982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74378, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74379 q = 1) (hb : d108983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74379, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11756 q = 1) (hb : d53134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27152 q ha hb
    | true =>
      simp only [d11756, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25053 q ha hb
  have h17 (q : Pattern) (ha : d11757 q = 1) (hb : d53135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11758 q = 1) (hb : d53136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d11758, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d11759 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11762 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27153 q ha hb
    | true =>
      simp only [d11762, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25054 q ha hb
  have h21 (q : Pattern) (ha : d11763 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11764 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d11764, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d11766 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27154 q ha hb
    | true =>
      simp only [d11766, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27142 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53145 q = 1) (hb : d108985 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d53145, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d11772 q = 1) (hb : d74382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27155 q ha hb
    | true =>
      simp only [d11772, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d11773 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d11773, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74384 q = 1) (hb : d108986 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74384, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74385 q = 1) (hb : d108987 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74385, d108987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74385, d108987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74386 q = 1) (hb : d108988 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74386, d108988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74386, d108988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74387 q = 1) (hb : d108989 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74387, d108989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74387, d108989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27157 (p : Pattern) (ha : d74394 p = 1) (hb : d108996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11766 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27154 q ha hb
    | true =>
      simp only [d11766, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27142 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53145 q = 1) (hb : d108985 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53145, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11772 q = 1) (hb : d74382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27155 q ha hb
    | true =>
      simp only [d11772, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11773 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11773, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74384 q = 1) (hb : d108986 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74384, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74392 q = 1) (hb : d108994 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74392, d108994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74392, d108994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74393 q = 1) (hb : d108995 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74393, d108995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74393, d108995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74394 q = 1) (hb : d108996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d108996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d108996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27158 (p : Pattern) (ha : d11817 p = 1) (hb : d53220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11805 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11805, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d11805, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11806 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11806, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11806, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11807 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11807, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11807, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11808 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11809 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11810 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11811 q = 1) (hb : d53208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11811, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11815 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11816 q = 1) (hb : d53219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d53219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11816, d53219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11817 q = 1) (hb : d53220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d53220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11817, d53220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27159 (p : Pattern) (ha : d11822 p = 1) (hb : d53225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11815 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11820 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11820, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11821 q = 1) (hb : d53224 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d53224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11821, d53224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11822 q = 1) (hb : d53225 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d53225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11822, d53225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27160 (p : Pattern) (ha : d11828 p = 1) (hb : d53231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11818 q = 1) (hb : d53221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27158 q ha hb
    | true =>
      simp only [d11818, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11819 q = 1) (hb : d53222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11819, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11823 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27159 q ha hb
    | true =>
      simp only [d11823, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11824 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11825 q = 1) (hb : d53228 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d53228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11825, d53228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11826 q = 1) (hb : d53229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d53229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11826, d53229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11827 q = 1) (hb : d53230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d53230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11827, d53230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11828 q = 1) (hb : d53231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d53231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11828, d53231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27161 (p : Pattern) (ha : d11836 p = 1) (hb : d53239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11823 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27159 q ha hb
    | true =>
      simp only [d11823, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11824 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11831 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25037 q ha hb
    | true =>
      simp only [d11831, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11832 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11833 q = 1) (hb : d53236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d53236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11833, d53236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11834 q = 1) (hb : d53237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d53237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11834, d53237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11835 q = 1) (hb : d53238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d53238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11835, d53238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11836 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d53239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11836, d53239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27162 (p : Pattern) (ha : d11869 p = 1) (hb : d74412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11815 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11864 q = 1) (hb : d74407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11864, d74407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9300 q ha hb
    | true =>
      simp only [d11864, d74407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11865 q = 1) (hb : d74408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11865, d74408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11865, d74408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11866 q = 1) (hb : d74409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11866, d74409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11866, d74409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11867 q = 1) (hb : d74410 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11867, d74410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11867, d74410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d11868 q = 1) (hb : d74411 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d74411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11868, d74411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11869 q = 1) (hb : d74412 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d74412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11869, d74412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27163 (p : Pattern) (ha : d11875 p = 1) (hb : d74418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11870 q = 1) (hb : d74413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d74413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27162 q ha hb
    | true =>
      simp only [d11870, d74413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11871 q = 1) (hb : d74414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d74414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11871, d74414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11872 q = 1) (hb : d74415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d74415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11872, d74415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11873 q = 1) (hb : d74416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d74416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11873, d74416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11874 q = 1) (hb : d74417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d74417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11874, d74417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11875 q = 1) (hb : d74418 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d74418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11875, d74418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27164 (p : Pattern) (ha : d74424 p = 1) (hb : d109006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11837 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27160 q ha hb
    | true =>
      simp only [d11837, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27161 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d109002 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d109002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d109002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11876 q = 1) (hb : d74419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d74419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27163 q ha hb
    | true =>
      simp only [d11876, d74419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11877 q = 1) (hb : d74420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d74420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11877, d74420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74421 q = 1) (hb : d109003 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d109003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d109003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74422 q = 1) (hb : d109004 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d109004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d109004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74423 q = 1) (hb : d109005 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d109005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d109005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74424 q = 1) (hb : d109006 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d109006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d109006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27165 (p : Pattern) (ha : d74430 p = 1) (hb : d109012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11667 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11667, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27141 q ha hb
  have h2 (q : Pattern) (ha : d11668 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11668, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11677 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27141 q ha hb
    | true =>
      simp only [d11677, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27143 q ha hb
  have h4 (q : Pattern) (ha : d11678 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11678, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11679 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11679, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74388 q = 1) (hb : d108990 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74388, d108990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27151 q ha hb
    | true =>
      simp only [d74388, d108990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27156 q ha hb
  have h7 (q : Pattern) (ha : d11791 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27144 q ha hb
    | true =>
      simp only [d11791, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25035 q ha hb
  have h8 (q : Pattern) (ha : d74389 q = 1) (hb : d108991 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74389, d108991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74389, d108991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74390 q = 1) (hb : d108992 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d108992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74390, d108992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74391 q = 1) (hb : d108993 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d108993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74391, d108993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74395 q = 1) (hb : d108997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d108997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74395, d108997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27157 q ha hb
  have h12 (q : Pattern) (ha : d11800 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11800, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25036 q ha hb
  have h13 (q : Pattern) (ha : d74396 q = 1) (hb : d108998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d108998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74396, d108998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74397 q = 1) (hb : d108999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d108999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74397, d108999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74398 q = 1) (hb : d109000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d109000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74398, d109000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74399 q = 1) (hb : d109001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d109001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74399, d109001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74425 q = 1) (hb : d109007 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d109007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74425, d109007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27164 q ha hb
  have h18 (q : Pattern) (ha : d11893 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11893, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25039 q ha hb
  have h19 (q : Pattern) (ha : d74426 q = 1) (hb : d109008 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d109008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74426, d109008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74427 q = 1) (hb : d109009 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d109009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74427, d109009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74428 q = 1) (hb : d109010 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d109010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74428, d109010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74429 q = 1) (hb : d109011 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d109011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74429, d109011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74430 q = 1) (hb : d109012 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d109012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74430, d109012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27166 (p : Pattern) (ha : d74436 p = 1) (hb : d109018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d109013 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d109013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d109013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27165 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d109014 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d109014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d109014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d109015 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d109015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d109015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d109016 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d109016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d109016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d109017 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d109017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d109017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d109018 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d109018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d109018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27167 (p : Pattern) (ha : d11918 p = 1) (hb : d53371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11915 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11916 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11916, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11917 q = 1) (hb : d53370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d53370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11917, d53370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11918 q = 1) (hb : d53371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d53371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11918, d53371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27168 (p : Pattern) (ha : d11928 p = 1) (hb : d53381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11928 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11928, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27169 (p : Pattern) (ha : d11938 p = 1) (hb : d53391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
    | true =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11938 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27170 (p : Pattern) (ha : d11941 p = 1) (hb : d53394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11941 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11941, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27171 (p : Pattern) (ha : d11948 p = 1) (hb : d53401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
    | true =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11943 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27170 q ha hb
    | true =>
      simp only [d11943, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q ha hb
  have h7 (q : Pattern) (ha : d11944 q = 1) (hb : d53397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11945 q = 1) (hb : d53398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11945, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11946 q = 1) (hb : d53399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11947 q = 1) (hb : d53400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11948 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11948, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27172 (p : Pattern) (ha : d12056 p = 1) (hb : d53475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
    | true =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12051 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
    | true =>
      simp only [d12051, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12052 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12053 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12053, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12054 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12055 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12056 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d53475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12056, d53475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27173 (p : Pattern) (ha : d11953 p = 1) (hb : d53406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11953 q = 1) (hb : d53406 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11953, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27174 (p : Pattern) (ha : d11962 p = 1) (hb : d53415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11962 q = 1) (hb : d53415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11962, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27175 (p : Pattern) (ha : d11974 p = 1) (hb : d53434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11969 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11969, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d11969, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11970 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11970, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11970, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11971 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11971, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11971, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11909 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11910 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11911 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11972 q = 1) (hb : d53432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11972, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11915 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11973 q = 1) (hb : d53433 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d53433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11973, d53433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11974 q = 1) (hb : d53434 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d53434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d11974, d53434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27176 (p : Pattern) (ha : d11980 p = 1) (hb : d53440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27175 q ha hb
    | true =>
      simp only [d11975, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d53437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d53438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11980 q = 1) (hb : d53440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d53440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11980, d53440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27177 (p : Pattern) (ha : d12013 p = 1) (hb : d74459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11915 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74453 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12008 q = 1) (hb : d74454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12008, d74454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9308 q ha hb
    | true =>
      simp only [d12008, d74454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12009 q = 1) (hb : d74455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12009, d74455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12009, d74455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12010 q = 1) (hb : d74456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12010, d74456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12010, d74456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12011 q = 1) (hb : d74457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12011, d74457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12011, d74457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d12012 q = 1) (hb : d74458 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d74458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12012, d74458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12013 q = 1) (hb : d74459 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d74459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12013, d74459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27178 (p : Pattern) (ha : d12019 p = 1) (hb : d74465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d74460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d74460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27177 q ha hb
    | true =>
      simp only [d12014, d74460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d74461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d74461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d74461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d74462 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d74462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d74462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d74463 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d74463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d74463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d74464 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d74464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d74464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12019 q = 1) (hb : d74465 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d74465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12019, d74465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27179 (p : Pattern) (ha : d74471 p = 1) (hb : d109027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27173 q ha hb
    | true =>
      simp only [d11956, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25083 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27174 q ha hb
    | true =>
      simp only [d11966, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25084 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27176 q ha hb
    | true =>
      simp only [d11981, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53442 q = 1) (hb : d109023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53442, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12020 q = 1) (hb : d74466 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27178 q ha hb
    | true =>
      simp only [d12020, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12021 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12021, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74468 q = 1) (hb : d109024 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74468, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74469 q = 1) (hb : d109025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74469, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74470 q = 1) (hb : d109026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74470, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74471 q = 1) (hb : d109027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74471, d109027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74471, d109027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27180 (p : Pattern) (ha : d12026 p = 1) (hb : d53449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12026 q = 1) (hb : d53449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12026, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27181 (p : Pattern) (ha : d12032 p = 1) (hb : d53455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12032 q = 1) (hb : d53455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12032, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27182 (p : Pattern) (ha : d12037 p = 1) (hb : d53460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27175 q ha hb
    | true =>
      simp only [d11975, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27167 q ha hb
    | true =>
      simp only [d11919, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d53437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d53438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12037 q = 1) (hb : d53460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d53460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12037, d53460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27183 (p : Pattern) (ha : d12043 p = 1) (hb : d74472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d74460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d74460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27177 q ha hb
    | true =>
      simp only [d12014, d74460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d74461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d74461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d74461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d74462 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d74462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d74462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d74463 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d74463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d74463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d74464 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d74464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d74464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12043 q = 1) (hb : d74472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d74472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12043, d74472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27184 (p : Pattern) (ha : d74478 p = 1) (hb : d109032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27173 q ha hb
    | true =>
      simp only [d11956, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25083 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27174 q ha hb
    | true =>
      simp only [d11966, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25084 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27176 q ha hb
    | true =>
      simp only [d11981, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53442 q = 1) (hb : d109023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53442, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12020 q = 1) (hb : d74466 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27178 q ha hb
    | true =>
      simp only [d12020, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12021 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12021, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74468 q = 1) (hb : d109024 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74468, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74469 q = 1) (hb : d109025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74469, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74470 q = 1) (hb : d109026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74470, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12028 q = 1) (hb : d53451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27180 q ha hb
    | true =>
      simp only [d12028, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25091 q ha hb
  have h17 (q : Pattern) (ha : d12029 q = 1) (hb : d53452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12029, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12030 q = 1) (hb : d53453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d12030, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d12031 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12031, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12034 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27181 q ha hb
    | true =>
      simp only [d12034, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25092 q ha hb
  have h21 (q : Pattern) (ha : d12035 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12035, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12036 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d12036, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d12038 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27182 q ha hb
    | true =>
      simp only [d12038, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27170 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53462 q = 1) (hb : d109028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d53462, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d12044 q = 1) (hb : d74473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27183 q ha hb
    | true =>
      simp only [d12044, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d12045 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d12045, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74475 q = 1) (hb : d109029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74475, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74476 q = 1) (hb : d109030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74476, d109030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74476, d109030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74477 q = 1) (hb : d109031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74477, d109031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74477, d109031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74478 q = 1) (hb : d109032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74478, d109032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74478, d109032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27185 (p : Pattern) (ha : d74485 p = 1) (hb : d109039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12038 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27182 q ha hb
    | true =>
      simp only [d12038, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27170 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53462 q = 1) (hb : d109028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53462, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d12044 q = 1) (hb : d74473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27183 q ha hb
    | true =>
      simp only [d12044, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12045 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12045, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74475 q = 1) (hb : d109029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74475, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74483 q = 1) (hb : d109037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74483, d109037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74483, d109037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74484 q = 1) (hb : d109038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74484, d109038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74484, d109038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74485 q = 1) (hb : d109039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d109039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d109039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27186 (p : Pattern) (ha : d12089 p = 1) (hb : d53537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12077 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12077, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d12077, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12078 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12078, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12078, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12079 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12079, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12079, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12080 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12081 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12082 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12083 q = 1) (hb : d53525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12083, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12087 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12088 q = 1) (hb : d53536 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d53536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12088, d53536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12089 q = 1) (hb : d53537 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d53537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12089, d53537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27187 (p : Pattern) (ha : d12094 p = 1) (hb : d53542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12087 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12092 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12092, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12093 q = 1) (hb : d53541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d53541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12093, d53541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12094 q = 1) (hb : d53542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d53542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12094, d53542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27188 (p : Pattern) (ha : d12100 p = 1) (hb : d53548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12090 q = 1) (hb : d53538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27186 q ha hb
    | true =>
      simp only [d12090, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12091 q = 1) (hb : d53539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12091, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12095 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27187 q ha hb
    | true =>
      simp only [d12095, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12096 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12097 q = 1) (hb : d53545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d53545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12097, d53545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12098 q = 1) (hb : d53546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d53546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12098, d53546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12099 q = 1) (hb : d53547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d53547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12099, d53547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12100 q = 1) (hb : d53548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d53548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12100, d53548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27189 (p : Pattern) (ha : d12108 p = 1) (hb : d53556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12095 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27187 q ha hb
    | true =>
      simp only [d12095, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12096 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12103 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25075 q ha hb
    | true =>
      simp only [d12103, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12104 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12105 q = 1) (hb : d53553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d53553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12105, d53553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12106 q = 1) (hb : d53554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d53554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12106, d53554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12107 q = 1) (hb : d53555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d53555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12107, d53555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12108 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d53556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12108, d53556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27190 (p : Pattern) (ha : d12141 p = 1) (hb : d74503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12087 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74497 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12136 q = 1) (hb : d74498 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12136, d74498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9316 q ha hb
    | true =>
      simp only [d12136, d74498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12137 q = 1) (hb : d74499 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12137, d74499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12137, d74499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12138 q = 1) (hb : d74500 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12138, d74500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12138, d74500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12139 q = 1) (hb : d74501 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12139, d74501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12139, d74501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d12140 q = 1) (hb : d74502 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d74502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12140, d74502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12141 q = 1) (hb : d74503 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d74503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12141, d74503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro27191 (p : Pattern) (ha : d12147 p = 1) (hb : d74509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12142 q = 1) (hb : d74504 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d74504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27190 q ha hb
    | true =>
      simp only [d12142, d74504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12143 q = 1) (hb : d74505 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d74505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12143, d74505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12144 q = 1) (hb : d74506 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d74506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12144, d74506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12145 q = 1) (hb : d74507 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d74507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12145, d74507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12146 q = 1) (hb : d74508 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d74508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12146, d74508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12147 q = 1) (hb : d74509 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d74509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12147, d74509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27192 (p : Pattern) (ha : d74515 p = 1) (hb : d109049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12109 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27188 q ha hb
    | true =>
      simp only [d12109, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27189 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d109045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d109045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d109045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d12148 q = 1) (hb : d74510 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d74510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27191 q ha hb
    | true =>
      simp only [d12148, d74510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12149 q = 1) (hb : d74511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d74511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12149, d74511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74512 q = 1) (hb : d109046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d109046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d109046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74513 q = 1) (hb : d109047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d109047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d109047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74514 q = 1) (hb : d109048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d109048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d109048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74515 q = 1) (hb : d109049 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d109049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d109049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27193 (p : Pattern) (ha : d74521 p = 1) (hb : d109055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11939 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11939, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27169 q ha hb
  have h2 (q : Pattern) (ha : d11940 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11940, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11949 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27169 q ha hb
    | true =>
      simp only [d11949, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27171 q ha hb
  have h4 (q : Pattern) (ha : d11950 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11950, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11951 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11951, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74479 q = 1) (hb : d109033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74479, d109033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27179 q ha hb
    | true =>
      simp only [d74479, d109033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27184 q ha hb
  have h7 (q : Pattern) (ha : d12063 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27172 q ha hb
    | true =>
      simp only [d12063, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25073 q ha hb
  have h8 (q : Pattern) (ha : d74480 q = 1) (hb : d109034 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74480, d109034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74480, d109034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74481 q = 1) (hb : d109035 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d109035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74481, d109035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74482 q = 1) (hb : d109036 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d109036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74482, d109036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74486 q = 1) (hb : d109040 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d109040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74486, d109040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27185 q ha hb
  have h12 (q : Pattern) (ha : d12072 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12072, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25074 q ha hb
  have h13 (q : Pattern) (ha : d74487 q = 1) (hb : d109041 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d109041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74487, d109041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74488 q = 1) (hb : d109042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d109042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74488, d109042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74489 q = 1) (hb : d109043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d109043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74489, d109043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74490 q = 1) (hb : d109044 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d109044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74490, d109044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74516 q = 1) (hb : d109050 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d109050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74516, d109050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27192 q ha hb
  have h18 (q : Pattern) (ha : d12165 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12165, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25077 q ha hb
  have h19 (q : Pattern) (ha : d74517 q = 1) (hb : d109051 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d109051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74517, d109051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74518 q = 1) (hb : d109052 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d109052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74518, d109052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74519 q = 1) (hb : d109053 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d109053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74519, d109053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74520 q = 1) (hb : d109054 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d109054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74520, d109054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74521 q = 1) (hb : d109055 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d109055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74521, d109055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27194 (p : Pattern) (ha : d74527 p = 1) (hb : d109061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d109056 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d109056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d109056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27193 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d109057 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d109057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d109057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d109058 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d109058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d109058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d109059 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d109059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d109059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d109060 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d109060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d109060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d109061 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d109061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d109061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27195 (p : Pattern) (ha : d74533 p = 1) (hb : d109067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d108896 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d108896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27056 q ha hb
    | true =>
      simp only [d74173, d108896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27082 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d108936 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d108936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d108936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27110 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d108937 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d108937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d108937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d108977 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d108977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d108977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27138 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d108978 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d108978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d108978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d108979 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d108979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d108979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d109019 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d109019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d109019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27166 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d109020 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d109020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d109020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d109021 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d109021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d109021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d109022 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d109022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d109022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d109062 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d109062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d109062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27194 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d109063 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d109063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d109063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d109064 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d109064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d109064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d109065 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d109065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d109065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d109066 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d109066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d109066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d109067 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d109067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d109067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro27196 (p : Pattern) (ha : d74539 p = 1) (hb : d109073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d109068 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d109068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27195 q ha hb
    | true =>
      simp only [d74534, d109068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d109069 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d109069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d109069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d109070 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d109070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d109070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d109071 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d109071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d109071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d109072 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d109072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d109072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d109073 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d109073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d109073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27197 (p : Pattern) (ha : d74545 p = 1) (hb : d109079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d109074 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d109074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27196 q ha hb
    | true =>
      simp only [d74540, d109074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d109075 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d109075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d109075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d109076 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d109076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d109076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d109077 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d109077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d109077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d109078 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d109078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d109078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d109079 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d109079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d109079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27198 (p : Pattern) (ha : d74551 p = 1) (hb : d109085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d109080 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d109080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27197 q ha hb
    | true =>
      simp only [d74546, d109080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d109081 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d109081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d109081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d109082 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d109082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d109082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d109083 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d109083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d109083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d109084 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d109084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d109084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d109085 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d109085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d109085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27199 (p : Pattern) (ha : d74557 p = 1) (hb : d109091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d109086 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d109086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27198 q ha hb
    | true =>
      simp only [d74552, d109086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d109087 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d109087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d109087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d109088 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d109088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d109088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d109089 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d109089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d109089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d109090 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d109091 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27200 (p : Pattern) (ha : d74563 p = 1) (hb : d109097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d109092 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27199 q ha hb
    | true =>
      simp only [d74558, d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d109093 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d109094 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d109095 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d109096 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d109097 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27201 (p : Pattern) (ha : d74569 p = 1) (hb : d109103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d109098 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27200 q ha hb
    | true =>
      simp only [d74564, d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d109099 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d109100 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d109101 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d109102 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d109103 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27202 (p : Pattern) (ha : d74575 p = 1) (hb : d109109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d109104 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27201 q ha hb
    | true =>
      simp only [d74570, d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d109105 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d109106 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d109107 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d109108 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d109109 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27203 (p : Pattern) (ha : d109322 p = 1) (hb : d135429 p = 1) : d109322 p = 1 := by
  have h0 (q : Pattern) (ha : d109322 q = 1) (hb : d135429 q = 1) : d109322 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro27204 (p : Pattern) (ha : d10719 p = 1) (hb : d74080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d10715 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10715, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10716 q = 1) (hb : d74077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10716, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10717 q = 1) (hb : d74078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10717, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10718 q = 1) (hb : d74079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10718, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10719 q = 1) (hb : d74080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d74080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d74080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27205 (p : Pattern) (ha : d10726 p = 1) (hb : d74087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10661 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27027 q ha hb
    | true =>
      simp only [d10661, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d10715 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10715, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10716 q = 1) (hb : d74077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10716, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10717 q = 1) (hb : d74078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10717, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10718 q = 1) (hb : d74079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10668 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
    | true =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d10722 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10722, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10723 q = 1) (hb : d74084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10723, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10724 q = 1) (hb : d74085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d74085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10724, d74085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10725 q = 1) (hb : d74086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d74086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10725, d74086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10726 q = 1) (hb : d74087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d74087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10726, d74087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27206 (p : Pattern) (ha : d74094 p = 1) (hb : d109112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27029 q ha hb
    | true =>
      simp only [d10668, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d10722 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10722, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10723 q = 1) (hb : d74084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10723, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10724 q = 1) (hb : d74092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d74092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d74092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10725 q = 1) (hb : d74093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d74093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d74093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74094 q = 1) (hb : d109112 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d109112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d109112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27207 (p : Pattern) (ha : d74109 p = 1) (hb : d109122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27033 q ha hb
    | true =>
      simp only [d10698, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d109118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d109118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52197, d109118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74106 q = 1) (hb : d109119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74106, d109119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74106, d109119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74107 q = 1) (hb : d109120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74107, d109120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74107, d109120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74108 q = 1) (hb : d109121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74108, d109121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74108, d109121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74109 q = 1) (hb : d109122 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74109, d109122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74109, d109122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27208 (p : Pattern) (ha : d74115 p = 1) (hb : d109128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d74088 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d74088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27204 q ha hb
    | true =>
      simp only [d10727, d74088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27205 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10728 q = 1) (hb : d74089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d74089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d74089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74090 q = 1) (hb : d109110 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74090, d109110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74090, d109110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74091 q = 1) (hb : d109111 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74091, d109111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74091, d109111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74095 q = 1) (hb : d109113 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74095, d109113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74095, d109113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27206 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74096 q = 1) (hb : d109114 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74096, d109114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74096, d109114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74097 q = 1) (hb : d109115 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74097, d109115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74097, d109115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74098 q = 1) (hb : d109116 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74098, d109116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74098, d109116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74099 q = 1) (hb : d109117 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74099, d109117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74099, d109117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74110 q = 1) (hb : d109123 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74110, d109123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74110, d109123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27207 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74111 q = 1) (hb : d109124 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74111, d109124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74111, d109124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74112 q = 1) (hb : d109125 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74112, d109125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74112, d109125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74113 q = 1) (hb : d109126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74113, d109126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74113, d109126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74114 q = 1) (hb : d109127 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74114, d109127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74114, d109127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74115 q = 1) (hb : d109128 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74115, d109128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74115, d109128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27209 (p : Pattern) (ha : d74121 p = 1) (hb : d109134 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d74116 q = 1) (hb : d109129 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74116, d109129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74116, d109129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27208 q ha hb
  have h8 (q : Pattern) (ha : d74117 q = 1) (hb : d109130 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74117, d109130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74117, d109130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74118 q = 1) (hb : d109131 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74118, d109131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74118, d109131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74119 q = 1) (hb : d109132 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74119, d109132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74119, d109132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74120 q = 1) (hb : d109133 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74120, d109133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74120, d109133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74121 q = 1) (hb : d109134 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74121, d109134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74121, d109134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27210 (p : Pattern) (ha : d10885 p = 1) (hb : d74131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10880 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
    | true =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
  have h5 (q : Pattern) (ha : d10881 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10881, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10882 q = 1) (hb : d74128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10882, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10883 q = 1) (hb : d74129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10883, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10884 q = 1) (hb : d74130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10884, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10885 q = 1) (hb : d74131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d74131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d74131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27211 (p : Pattern) (ha : d10895 p = 1) (hb : d74138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10880 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27058 q ha hb
    | true =>
      simp only [d10880, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
  have h4 (q : Pattern) (ha : d10881 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10881, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10882 q = 1) (hb : d74128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10882, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10883 q = 1) (hb : d74129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10883, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10884 q = 1) (hb : d74130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10890 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27060 q ha hb
    | true =>
      simp only [d10890, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q ha hb
  have h13 (q : Pattern) (ha : d10891 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10891, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10892 q = 1) (hb : d74135 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10892, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10893 q = 1) (hb : d74136 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d74136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10893, d74136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10894 q = 1) (hb : d74137 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d74137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10894, d74137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10895 q = 1) (hb : d74138 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d74138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10895, d74138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27212 (p : Pattern) (ha : d74145 p = 1) (hb : d109137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10890 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27060 q ha hb
    | true =>
      simp only [d10890, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q ha hb
  have h3 (q : Pattern) (ha : d10891 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10891, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10892 q = 1) (hb : d74135 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10892, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10893 q = 1) (hb : d74143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d74143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d74143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10894 q = 1) (hb : d74144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d74144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d74144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74145 q = 1) (hb : d109137 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74145, d109137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74145, d109137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27213 (p : Pattern) (ha : d74160 p = 1) (hb : d109148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52399 q = 1) (hb : d109143 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52399, d109143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27078 q hb ha
    | true =>
      simp only [d52399, d109143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24926 q hb ha
  have h3 (q : Pattern) (ha : d52400 q = 1) (hb : d109144 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d109144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52400, d109144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74157 q = 1) (hb : d109145 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74157, d109145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74157, d109145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74158 q = 1) (hb : d109146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74158, d109146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74158, d109146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74159 q = 1) (hb : d109147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74159, d109147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74159, d109147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74160 q = 1) (hb : d109148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74160, d109148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74160, d109148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27214 (p : Pattern) (ha : d74166 p = 1) (hb : d109154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d74139 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d74139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27210 q ha hb
    | true =>
      simp only [d10896, d74139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27211 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10897 q = 1) (hb : d74140 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d74140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d74140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74141 q = 1) (hb : d109135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74141, d109135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74141, d109135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74142 q = 1) (hb : d109136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74142, d109136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74142, d109136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74146 q = 1) (hb : d109138 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74146, d109138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74146, d109138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27212 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74147 q = 1) (hb : d109139 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74147, d109139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74147, d109139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74148 q = 1) (hb : d109140 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74148, d109140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74148, d109140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74149 q = 1) (hb : d109141 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74149, d109141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74149, d109141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74150 q = 1) (hb : d109142 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74150, d109142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74150, d109142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74161 q = 1) (hb : d109149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74161, d109149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74161, d109149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27213 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74162 q = 1) (hb : d109150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74162, d109150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74162, d109150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74163 q = 1) (hb : d109151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74163, d109151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74163, d109151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74164 q = 1) (hb : d109152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74164, d109152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74164, d109152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74165 q = 1) (hb : d109153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74165, d109153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74165, d109153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74166 q = 1) (hb : d109154 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74166, d109154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74166, d109154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27215 (p : Pattern) (ha : d74172 p = 1) (hb : d109160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74167 q = 1) (hb : d109155 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74167, d109155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74167, d109155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27214 q ha hb
  have h2 (q : Pattern) (ha : d74168 q = 1) (hb : d109156 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74168, d109156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74168, d109156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74169 q = 1) (hb : d109157 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74169, d109157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74169, d109157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74170 q = 1) (hb : d109158 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74170, d109158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74170, d109158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74171 q = 1) (hb : d109159 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74171, d109159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74171, d109159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74172 q = 1) (hb : d109160 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74172, d109160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74172, d109160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27216 (p : Pattern) (ha : d11125 p = 1) (hb : d74201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11120 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
    | true =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
  have h5 (q : Pattern) (ha : d11121 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11121, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11122 q = 1) (hb : d74198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11122, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11123 q = 1) (hb : d74199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11123, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11124 q = 1) (hb : d74200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11124, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11125 q = 1) (hb : d74201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d74201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d74201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27217 (p : Pattern) (ha : d11135 p = 1) (hb : d74208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11120 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27084 q ha hb
    | true =>
      simp only [d11120, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
  have h4 (q : Pattern) (ha : d11121 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11121, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11122 q = 1) (hb : d74198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11122, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11123 q = 1) (hb : d74199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11123, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11124 q = 1) (hb : d74200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11130 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27086 q ha hb
    | true =>
      simp only [d11130, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q ha hb
  have h13 (q : Pattern) (ha : d11131 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11131, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11132 q = 1) (hb : d74205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11132, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11133 q = 1) (hb : d74206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d74206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11133, d74206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11134 q = 1) (hb : d74207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d74207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11134, d74207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11135 q = 1) (hb : d74208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d74208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11135, d74208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27218 (p : Pattern) (ha : d74215 p = 1) (hb : d109164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11130 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27086 q ha hb
    | true =>
      simp only [d11130, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q ha hb
  have h3 (q : Pattern) (ha : d11131 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11131, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11132 q = 1) (hb : d74205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11132, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11133 q = 1) (hb : d74213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d74213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d74213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11134 q = 1) (hb : d74214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d74214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d74214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74215 q = 1) (hb : d109164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74215, d109164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74215, d109164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27219 (p : Pattern) (ha : d74245 p = 1) (hb : d109175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52636 q = 1) (hb : d109170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52636, d109170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27105 q hb ha
    | true =>
      simp only [d52636, d109170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24962 q hb ha
  have h3 (q : Pattern) (ha : d52637 q = 1) (hb : d109171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d109171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52637, d109171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74241 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74242 q = 1) (hb : d109172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74242, d109172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74242, d109172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74243 q = 1) (hb : d109173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74243, d109173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74243, d109173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74244 q = 1) (hb : d109174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74244, d109174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74244, d109174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74245 q = 1) (hb : d109175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74245, d109175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74245, d109175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27220 (p : Pattern) (ha : d74251 p = 1) (hb : d109181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d74209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d74209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27216 q ha hb
    | true =>
      simp only [d11136, d74209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27217 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11137 q = 1) (hb : d74210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d74210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d74210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74211 q = 1) (hb : d109162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74211, d109162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74211, d109162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74212 q = 1) (hb : d109163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74212, d109163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74212, d109163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74216 q = 1) (hb : d109165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74216, d109165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74216, d109165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27218 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74217 q = 1) (hb : d109166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74217, d109166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74217, d109166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74218 q = 1) (hb : d109167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74218, d109167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74218, d109167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74219 q = 1) (hb : d109168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74219, d109168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74219, d109168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74220 q = 1) (hb : d109169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74220, d109169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74220, d109169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74246 q = 1) (hb : d109176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74246, d109176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74246, d109176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27219 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74247 q = 1) (hb : d109177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74247, d109177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74247, d109177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74248 q = 1) (hb : d109178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74248, d109178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74248, d109178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74249 q = 1) (hb : d109179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74249, d109179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74249, d109179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74250 q = 1) (hb : d109180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74250, d109180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74250, d109180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74251 q = 1) (hb : d109181 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74251, d109181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74251, d109181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27221 (p : Pattern) (ha : d74257 p = 1) (hb : d109187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74252 q = 1) (hb : d109182 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74252, d109182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74252, d109182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27220 q ha hb
  have h2 (q : Pattern) (ha : d74253 q = 1) (hb : d109183 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74253, d109183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74253, d109183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74254 q = 1) (hb : d109184 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74254, d109184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74254, d109184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74255 q = 1) (hb : d109185 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74255, d109185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74255, d109185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74256 q = 1) (hb : d109186 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74256, d109186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74256, d109186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74257 q = 1) (hb : d109187 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74257, d109187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74257, d109187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27222 (p : Pattern) (ha : d11395 p = 1) (hb : d74290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11390 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
    | true =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
  have h5 (q : Pattern) (ha : d11391 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11391, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11392 q = 1) (hb : d74287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11392, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11393 q = 1) (hb : d74288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11393, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11394 q = 1) (hb : d74289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11394, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11395 q = 1) (hb : d74290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d74290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d74290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27223 (p : Pattern) (ha : d11405 p = 1) (hb : d74297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11390 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27112 q ha hb
    | true =>
      simp only [d11390, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
  have h4 (q : Pattern) (ha : d11391 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11391, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11392 q = 1) (hb : d74287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11392, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11393 q = 1) (hb : d74288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11393, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11394 q = 1) (hb : d74289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11400 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27114 q ha hb
    | true =>
      simp only [d11400, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q ha hb
  have h13 (q : Pattern) (ha : d11401 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11401, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11402 q = 1) (hb : d74294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11402, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11403 q = 1) (hb : d74295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d74295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11403, d74295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11404 q = 1) (hb : d74296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d74296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11404, d74296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11405 q = 1) (hb : d74297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d74297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11405, d74297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27224 (p : Pattern) (ha : d74304 p = 1) (hb : d109192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11400 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27114 q ha hb
    | true =>
      simp only [d11400, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q ha hb
  have h3 (q : Pattern) (ha : d11401 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11401, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11402 q = 1) (hb : d74294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11402, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11403 q = 1) (hb : d74302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d74302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d74302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11404 q = 1) (hb : d74303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d74303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d74303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74304 q = 1) (hb : d109192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d109192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d109192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27225 (p : Pattern) (ha : d74334 p = 1) (hb : d109203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d109198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d109198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27133 q hb ha
    | true =>
      simp only [d52930, d109198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25000 q hb ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d109199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d109199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d109199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74331 q = 1) (hb : d109200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d109200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d109200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74332 q = 1) (hb : d109201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d109201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d109201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74333 q = 1) (hb : d109202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d109202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d109202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74334 q = 1) (hb : d109203 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d109203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d109203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27226 (p : Pattern) (ha : d74340 p = 1) (hb : d109209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d74298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d74298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27222 q ha hb
    | true =>
      simp only [d11406, d74298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27223 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11407 q = 1) (hb : d74299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d74299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d74299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74300 q = 1) (hb : d109190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d109190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74300, d109190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74301 q = 1) (hb : d109191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d109191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74301, d109191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74305 q = 1) (hb : d109193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d109193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74305, d109193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27224 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74306 q = 1) (hb : d109194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d109194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74306, d109194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74307 q = 1) (hb : d109195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d109195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74307, d109195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74308 q = 1) (hb : d109196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d109196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74308, d109196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74309 q = 1) (hb : d109197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d109197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74309, d109197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74335 q = 1) (hb : d109204 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d109204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74335, d109204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27225 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74336 q = 1) (hb : d109205 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d109205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74336, d109205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74337 q = 1) (hb : d109206 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d109206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74337, d109206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74338 q = 1) (hb : d109207 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d109207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74338, d109207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74339 q = 1) (hb : d109208 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d109208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74339, d109208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74340 q = 1) (hb : d109209 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d109209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74340, d109209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27227 (p : Pattern) (ha : d74346 p = 1) (hb : d109215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d109210 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d109210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d109210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27226 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d109211 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d109211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d109211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d109212 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d109212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d109212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d109213 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d109213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d109213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d109214 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d109214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d109214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d109215 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d109215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d109215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27228 (p : Pattern) (ha : d11666 p = 1) (hb : d74380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11661 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
    | true =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
  have h5 (q : Pattern) (ha : d11662 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11662, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11663 q = 1) (hb : d74377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11663, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11664 q = 1) (hb : d74378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11664, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11665 q = 1) (hb : d74379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11665, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11666 q = 1) (hb : d74380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d74380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d74380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27229 (p : Pattern) (ha : d11676 p = 1) (hb : d74387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11661 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27140 q ha hb
    | true =>
      simp only [d11661, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
  have h4 (q : Pattern) (ha : d11662 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11662, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11663 q = 1) (hb : d74377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11663, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11664 q = 1) (hb : d74378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11664, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11665 q = 1) (hb : d74379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11671 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27142 q ha hb
    | true =>
      simp only [d11671, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q ha hb
  have h13 (q : Pattern) (ha : d11672 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11672, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11673 q = 1) (hb : d74384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11673, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11674 q = 1) (hb : d74385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d74385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11674, d74385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11675 q = 1) (hb : d74386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d74386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11675, d74386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11676 q = 1) (hb : d74387 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d74387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11676, d74387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27230 (p : Pattern) (ha : d74394 p = 1) (hb : d109221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11671 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27142 q ha hb
    | true =>
      simp only [d11671, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q ha hb
  have h3 (q : Pattern) (ha : d11672 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11672, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11673 q = 1) (hb : d74384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11673, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11674 q = 1) (hb : d74392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d74392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d74392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11675 q = 1) (hb : d74393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d74393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d74393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74394 q = 1) (hb : d109221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d109221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d109221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27231 (p : Pattern) (ha : d74424 p = 1) (hb : d109232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d109227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d109227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27161 q hb ha
    | true =>
      simp only [d53245, d109227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25038 q hb ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d109228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d109228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d109228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74421 q = 1) (hb : d109229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d109229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d109229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74422 q = 1) (hb : d109230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d109230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d109230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74423 q = 1) (hb : d109231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d109231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d109231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74424 q = 1) (hb : d109232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d109232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d109232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27232 (p : Pattern) (ha : d74430 p = 1) (hb : d109238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d74388 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d74388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27228 q ha hb
    | true =>
      simp only [d11677, d74388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27229 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11678 q = 1) (hb : d74389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d74389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d74389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74390 q = 1) (hb : d109219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d109219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74390, d109219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74391 q = 1) (hb : d109220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d109220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74391, d109220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74395 q = 1) (hb : d109222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d109222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74395, d109222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27230 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74396 q = 1) (hb : d109223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d109223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74396, d109223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74397 q = 1) (hb : d109224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d109224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74397, d109224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74398 q = 1) (hb : d109225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d109225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74398, d109225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74399 q = 1) (hb : d109226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d109226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74399, d109226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74425 q = 1) (hb : d109233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d109233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74425, d109233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27231 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74426 q = 1) (hb : d109234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d109234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74426, d109234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74427 q = 1) (hb : d109235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d109235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74427, d109235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74428 q = 1) (hb : d109236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d109236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74428, d109236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74429 q = 1) (hb : d109237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d109237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74429, d109237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74430 q = 1) (hb : d109238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d109238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74430, d109238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27233 (p : Pattern) (ha : d74436 p = 1) (hb : d109244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d109239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d109239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d109239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27232 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d109240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d109240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d109240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d109241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d109241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d109241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d109242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d109242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d109242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d109243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d109243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d109243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d109244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d109244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d109244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27234 (p : Pattern) (ha : d11938 p = 1) (hb : d74471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11933 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
    | true =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
  have h5 (q : Pattern) (ha : d11934 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11934, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11935 q = 1) (hb : d74468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11935, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11936 q = 1) (hb : d74469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11936, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11937 q = 1) (hb : d74470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11937, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11938 q = 1) (hb : d74471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d74471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d74471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27235 (p : Pattern) (ha : d11948 p = 1) (hb : d74478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11933 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27168 q ha hb
    | true =>
      simp only [d11933, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
  have h4 (q : Pattern) (ha : d11934 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11934, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11935 q = 1) (hb : d74468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11935, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11936 q = 1) (hb : d74469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11936, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11937 q = 1) (hb : d74470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11943 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27170 q ha hb
    | true =>
      simp only [d11943, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q ha hb
  have h13 (q : Pattern) (ha : d11944 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11944, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11945 q = 1) (hb : d74475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11945, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11946 q = 1) (hb : d74476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d74476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11946, d74476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11947 q = 1) (hb : d74477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d74477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11947, d74477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11948 q = 1) (hb : d74478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d74478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11948, d74478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27236 (p : Pattern) (ha : d74485 p = 1) (hb : d109251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11943 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27170 q ha hb
    | true =>
      simp only [d11943, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q ha hb
  have h3 (q : Pattern) (ha : d11944 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11944, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11945 q = 1) (hb : d74475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11945, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11946 q = 1) (hb : d74483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d74483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d74483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11947 q = 1) (hb : d74484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d74484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d74484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74485 q = 1) (hb : d109251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d109251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d109251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27237 (p : Pattern) (ha : d74515 p = 1) (hb : d109262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d109257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d109257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27189 q hb ha
    | true =>
      simp only [d53562, d109257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25076 q hb ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d109258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d109258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d109258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74512 q = 1) (hb : d109259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d109259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d109259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74513 q = 1) (hb : d109260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d109260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d109260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74514 q = 1) (hb : d109261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d109261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d109261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74515 q = 1) (hb : d109262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d109262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d109262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27238 (p : Pattern) (ha : d74521 p = 1) (hb : d109268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d74479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d74479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27234 q ha hb
    | true =>
      simp only [d11949, d74479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27235 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11950 q = 1) (hb : d74480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d74480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d74480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74481 q = 1) (hb : d109249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d109249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74481, d109249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74482 q = 1) (hb : d109250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d109250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74482, d109250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74486 q = 1) (hb : d109252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d109252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74486, d109252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27236 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74487 q = 1) (hb : d109253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d109253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74487, d109253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74488 q = 1) (hb : d109254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d109254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74488, d109254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74489 q = 1) (hb : d109255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d109255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74489, d109255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74490 q = 1) (hb : d109256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d109256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74490, d109256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74516 q = 1) (hb : d109263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d109263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74516, d109263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27237 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74517 q = 1) (hb : d109264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d109264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74517, d109264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74518 q = 1) (hb : d109265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d109265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74518, d109265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74519 q = 1) (hb : d109266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d109266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74519, d109266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74520 q = 1) (hb : d109267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d109267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74520, d109267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74521 q = 1) (hb : d109268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d109268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74521, d109268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27239 (p : Pattern) (ha : d74527 p = 1) (hb : d109274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d109269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d109269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d109269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27238 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d109270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d109270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d109270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d109271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d109271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d109271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d109272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d109272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d109272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d109273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d109273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d109273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d109274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d109274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d109274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27240 (p : Pattern) (ha : d74533 p = 1) (hb : d109280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d109161 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d109161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27209 q ha hb
    | true =>
      simp only [d74173, d109161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27215 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d109188 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d109188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d109188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27221 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d109189 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d109189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d109189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d109216 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d109216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d109216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27227 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d109217 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d109217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d109217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d109218 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d109218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d109218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d109245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d109245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d109245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27233 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d109246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d109246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d109246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d109247 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d109247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d109247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d109248 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d109248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d109248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d109275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d109275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d109275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27239 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d109276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d109276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d109276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d109277 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d109277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d109277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d109278 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d109278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d109278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d109279 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d109279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d109279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d109280 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d109280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d109280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro27241 (p : Pattern) (ha : d74539 p = 1) (hb : d109286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d109281 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d109281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27240 q ha hb
    | true =>
      simp only [d74534, d109281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d109282 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d109282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d109282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d109283 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d109283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d109283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d109284 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d109284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d109284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d109285 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d109285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d109285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d109286 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d109286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d109286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27242 (p : Pattern) (ha : d74545 p = 1) (hb : d109292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d109287 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d109287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27241 q ha hb
    | true =>
      simp only [d74540, d109287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d109288 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d109288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d109288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d109289 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d109289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d109289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d109290 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d109290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d109290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d109291 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d109291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d109291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d109292 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d109292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d109292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27243 (p : Pattern) (ha : d74551 p = 1) (hb : d109298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d109293 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d109293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27242 q ha hb
    | true =>
      simp only [d74546, d109293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d109294 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d109294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d109294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d109295 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d109295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d109295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d109296 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d109296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d109296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d109297 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d109297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d109297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d109298 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d109298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d109298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27244 (p : Pattern) (ha : d74557 p = 1) (hb : d109304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d109299 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27243 q ha hb
    | true =>
      simp only [d74552, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d109300 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d109301 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d109302 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d109303 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d109304 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27245 (p : Pattern) (ha : d74563 p = 1) (hb : d109310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d109305 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27244 q ha hb
    | true =>
      simp only [d74558, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d109306 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d109307 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d109308 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d109309 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d109310 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27246 (p : Pattern) (ha : d74569 p = 1) (hb : d109316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d109311 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27245 q ha hb
    | true =>
      simp only [d74564, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d109312 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d109313 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d109314 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d109315 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d109316 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27247 (p : Pattern) (ha : d74575 p = 1) (hb : d109322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d109317 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27246 q ha hb
    | true =>
      simp only [d74570, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d109318 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d109319 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d109320 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d109321 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d109322 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27248 (p : Pattern) (ha : d10719 p = 1) (hb : d74579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d10715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d10715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4371, d10715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10716 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d10716, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10717 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10717, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10718 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10718, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10719 q = 1) (hb : d74579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27249 (p : Pattern) (ha : d10726 p = 1) (hb : d74583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10661 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4371 q = 1) (hb : d10715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d10715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4371, d10715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10716 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d10716, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10717 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10717, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10718 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10668 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4376 q = 1) (hb : d10722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d10722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4376, d10722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10723 q = 1) (hb : d74580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d10723, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10724 q = 1) (hb : d74581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d74581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10724, d74581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10725 q = 1) (hb : d74582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d74582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10725, d74582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10726 q = 1) (hb : d74583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d74583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10726, d74583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
end NetHack.Soko22Hazard87
