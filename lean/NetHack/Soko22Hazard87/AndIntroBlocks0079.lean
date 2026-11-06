import NetHack.Soko22Hazard87.AndIntroBlocks0078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro19750 (p : Pattern) (ha : d115507 p = 1) (hb : d116688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115503 q = 1) (hb : d116684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d116684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115503, d116684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d116685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d116685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115504, d116685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d116686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d116686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d116686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d116687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d116687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d116687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d116688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d116688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d116688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19751 (p : Pattern) (ha : d115513 p = 1) (hb : d116694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13653 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115491 q = 1) (hb : d116347 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19747 q ha hb
    | true =>
      simp only [d115491, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19748 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115492 q = 1) (hb : d116348 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115492, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115493 q = 1) (hb : d116671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d116671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115493, d116671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115494 q = 1) (hb : d116672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d116672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115494, d116672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115498 q = 1) (hb : d116674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d116674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115498, d116674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19749 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13803 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115499 q = 1) (hb : d116675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d116675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115499, d116675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115500 q = 1) (hb : d116676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d116676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115500, d116676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115501 q = 1) (hb : d116677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d116677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115501, d116677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115502 q = 1) (hb : d116678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d116678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115502, d116678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115508 q = 1) (hb : d116689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d116689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115508, d116689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19750 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13920 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115509 q = 1) (hb : d116690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d116690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115509, d116690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115510 q = 1) (hb : d116691 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d116691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115510, d116691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115511 q = 1) (hb : d116692 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d116692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115511, d116692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115512 q = 1) (hb : d116693 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d116693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115512, d116693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115513 q = 1) (hb : d116694 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d116694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115513, d116694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19752 (p : Pattern) (ha : d115519 p = 1) (hb : d116700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d116695 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d116695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d116695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19751 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d116696 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d116696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d116696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d116697 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d116697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d116697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d116698 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d116698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d116698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d116699 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d116699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d116699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d116700 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d116700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d116700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19753 (p : Pattern) (ha : d115525 p = 1) (hb : d116706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d116575 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d116575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19722 q ha hb
    | true =>
      simp only [d115354, d116575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19728 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d116602 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d116602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d116602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19734 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d116603 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d116603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d116603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d116634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d116634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d116634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19740 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d116635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d116635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d116635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d116636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d116636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d116636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d116667 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d116667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d116667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19746 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d116668 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d116668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d116668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d116669 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d116669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d116669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d116670 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d116670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d116670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d116701 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d116701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d116701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19752 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d116702 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d116702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d116702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d116703 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d116703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d116703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d116704 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d116704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d116704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d116705 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d116705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d116705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d116706 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d116706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d116706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro19754 (p : Pattern) (ha : d115531 p = 1) (hb : d116712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d116707 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d116707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19753 q ha hb
    | true =>
      simp only [d115526, d116707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d116708 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d116708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d116708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d116709 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d116709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d116709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d116710 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d116710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d116710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d116711 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d116711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d116711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d116712 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d116712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d116712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19755 (p : Pattern) (ha : d115537 p = 1) (hb : d116718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d116713 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d116713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19754 q ha hb
    | true =>
      simp only [d115532, d116713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d116714 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d116714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d116714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d116715 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d116715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d116715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d116716 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d116716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d116716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d116717 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d116717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d116717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d116718 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d116718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d116718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19756 (p : Pattern) (ha : d115543 p = 1) (hb : d116724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d116719 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d116719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19755 q ha hb
    | true =>
      simp only [d115538, d116719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d116720 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d116720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d116720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d116721 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d116721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d116721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d116722 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d116722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d116722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d116723 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d116723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d116723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d116724 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d116724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d116724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19757 (p : Pattern) (ha : d115549 p = 1) (hb : d116730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d116725 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d116725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19756 q ha hb
    | true =>
      simp only [d115544, d116725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d116726 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d116726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d116726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d116727 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d116727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d116727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d116728 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d116728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d116728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d116729 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d116729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d116729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d116730 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d116730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d116730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19758 (p : Pattern) (ha : d115555 p = 1) (hb : d116736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d116731 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d116731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19757 q ha hb
    | true =>
      simp only [d115550, d116731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d116732 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d116732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d116732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d116733 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d116733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d116733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d116734 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d116734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d116734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d116735 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d116735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d116735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d116736 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d116736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d116736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19759 (p : Pattern) (ha : d115561 p = 1) (hb : d116742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d116737 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d116737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19758 q ha hb
    | true =>
      simp only [d115556, d116737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d116738 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d116738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d116738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d116739 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d116739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d116739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d116740 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d116740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d116740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d116741 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d116741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d116741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d116742 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d116742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d116742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19760 (p : Pattern) (ha : d115567 p = 1) (hb : d116748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d116743 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d116743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19759 q ha hb
    | true =>
      simp only [d115562, d116743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d116744 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d116744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d116744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d116745 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d116745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d116745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d116746 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d116746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d116746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d116747 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d116747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d116747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d116748 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d116748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d116748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19761 (p : Pattern) (ha : d30 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d30, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19762 (p : Pattern) (ha : d36 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d34 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d35 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19763 (p : Pattern) (ha : d42 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19764 (p : Pattern) (ha : d48 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19765 (p : Pattern) (ha : d49 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19766 (p : Pattern) (ha : d55 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19767 (p : Pattern) (ha : d60 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19768 (p : Pattern) (ha : d71 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19769 (p : Pattern) (ha : d77 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19770 (p : Pattern) (ha : d83 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19769 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19771 (p : Pattern) (ha : d89 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19772 (p : Pattern) (ha : d95 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19764 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19766 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19767 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19771 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19773 (p : Pattern) (ha : d104 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19774 (p : Pattern) (ha : d111 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19775 (p : Pattern) (ha : d213 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19776 (p : Pattern) (ha : d116 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19777 (p : Pattern) (ha : d123 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19778 (p : Pattern) (ha : d144 p = 1) (hb : d116752 p = 1) : d120066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29 q = 1) (hb : d116750 q = 1) : d29 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144 q = 1) (hb : d116752 q = 1) : d120066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d116752, d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144, d116752, d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19779 (p : Pattern) (ha : d6739 p = 1) (hb : d116753 p = 1) : d120072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19778 q ha hb
    | true =>
      simp only [d145, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d34 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d34, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6738 q = 1) (hb : d116753 q = 1) : d120071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6738, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6738, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6739 q = 1) (hb : d116753 q = 1) : d120072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6739, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6739, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19780 (p : Pattern) (ha : d8238 p = 1) (hb : d116753 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8237 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8237, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8238 q = 1) (hb : d116753 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19781 (p : Pattern) (ha : d94191 p = 1) (hb : d116753 p = 1) : d120084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8239 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
    | true =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h9 (q : Pattern) (ha : d94187 q = 1) (hb : d116753 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94187, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94188 q = 1) (hb : d116753 q = 1) : d120081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94188, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94189 q = 1) (hb : d116753 q = 1) : d120082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94189, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94190 q = 1) (hb : d116753 q = 1) : d120083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94190, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94191 q = 1) (hb : d116753 q = 1) : d120084 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94191, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19782 (p : Pattern) (ha : d194 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19783 (p : Pattern) (ha : d199 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19784 (p : Pattern) (ha : d8245 p = 1) (hb : d116753 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8237 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8237, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8245 q = 1) (hb : d116753 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8245, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19785 (p : Pattern) (ha : d94196 p = 1) (hb : d116753 p = 1) : d120091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8239 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
    | true =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h9 (q : Pattern) (ha : d94187 q = 1) (hb : d116753 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94187, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94188 q = 1) (hb : d116753 q = 1) : d120081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94188, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94189 q = 1) (hb : d116753 q = 1) : d120082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94189, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94190 q = 1) (hb : d116753 q = 1) : d120083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94190, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19782 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19783 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8246 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19784 q ha hb
    | true =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h23 (q : Pattern) (ha : d94192 q = 1) (hb : d116753 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94192, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94193 q = 1) (hb : d116753 q = 1) : d120088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94193, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94194 q = 1) (hb : d116753 q = 1) : d120089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94194, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94195 q = 1) (hb : d116753 q = 1) : d120090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94195, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94196 q = 1) (hb : d116753 q = 1) : d120091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94196, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro19786 (p : Pattern) (ha : d94203 p = 1) (hb : d116753 p = 1) : d120096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8246 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19784 q ha hb
    | true =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h2 (q : Pattern) (ha : d94192 q = 1) (hb : d116753 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94192, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94193 q = 1) (hb : d116753 q = 1) : d120088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94193, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94201 q = 1) (hb : d116753 q = 1) : d120089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94201, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94202 q = 1) (hb : d116753 q = 1) : d120090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94202, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94203 q = 1) (hb : d116753 q = 1) : d120096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94203, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19787 (p : Pattern) (ha : d231 p = 1) (hb : d116752 p = 1) : d120102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d230 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70 q = 1) (hb : d116750 q = 1) : d70 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231 q = 1) (hb : d116752 q = 1) : d120102 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d116752, d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231, d116752, d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19788 (p : Pattern) (ha : d6772 p = 1) (hb : d116753 p = 1) : d120108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19787 q ha hb
    | true =>
      simp only [d232, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d73 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6771 q = 1) (hb : d116753 q = 1) : d120107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6771, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6771, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6772 q = 1) (hb : d116753 q = 1) : d120108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6772, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6772, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19789 (p : Pattern) (ha : d8267 p = 1) (hb : d116753 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19788 q ha hb
    | true =>
      simp only [d6773, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19769 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8264 q = 1) (hb : d116753 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8264, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8265 q = 1) (hb : d116753 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8265, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8266 q = 1) (hb : d116753 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8266, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8267 q = 1) (hb : d116753 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8267, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19790 (p : Pattern) (ha : d94213 p = 1) (hb : d116753 p = 1) : d120120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8268 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19789 q ha hb
    | true =>
      simp only [d8268, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
  have h2 (q : Pattern) (ha : d94209 q = 1) (hb : d116753 q = 1) : d120116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94209, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94210 q = 1) (hb : d116753 q = 1) : d120117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94210, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94211 q = 1) (hb : d116753 q = 1) : d120118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94211, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94212 q = 1) (hb : d116753 q = 1) : d120119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94212, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94213 q = 1) (hb : d116753 q = 1) : d120120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94213, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19791 (p : Pattern) (ha : d94219 p = 1) (hb : d116753 p = 1) : d120126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19773 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19773 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19774 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94197 q = 1) (hb : d116753 q = 1) : d120092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19781 q ha hb
    | true =>
      simp only [d94197, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19785 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19775 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94198 q = 1) (hb : d116753 q = 1) : d120093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94198, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94199 q = 1) (hb : d116753 q = 1) : d120094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94199, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94200 q = 1) (hb : d116753 q = 1) : d120095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94200, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94204 q = 1) (hb : d116753 q = 1) : d120097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94204, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19786 q ha hb
  have h12 (q : Pattern) (ha : d94205 q = 1) (hb : d116753 q = 1) : d120098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94205, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94206 q = 1) (hb : d116753 q = 1) : d120099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94206, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94207 q = 1) (hb : d116753 q = 1) : d120100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94207, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94208 q = 1) (hb : d116753 q = 1) : d120101 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94208, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94214 q = 1) (hb : d116753 q = 1) : d120121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94214, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19790 q ha hb
  have h17 (q : Pattern) (ha : d94215 q = 1) (hb : d116753 q = 1) : d120122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94215, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d94216 q = 1) (hb : d116753 q = 1) : d120123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94216, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d94217 q = 1) (hb : d116753 q = 1) : d120124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94217, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d94218 q = 1) (hb : d116753 q = 1) : d120125 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94218, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94219 q = 1) (hb : d116753 q = 1) : d120126 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94219, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro19792 (p : Pattern) (ha : d406 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19793 (p : Pattern) (ha : d462 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
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
theorem andIntro19794 (p : Pattern) (ha : d8289 p = 1) (hb : d116753 p = 1) : d120136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8239 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
    | true =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h2 (q : Pattern) (ha : d8285 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8286 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8286, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8287 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8288 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8289 q = 1) (hb : d116753 q = 1) : d120136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19795 (p : Pattern) (ha : d8296 p = 1) (hb : d116753 p = 1) : d120143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8239 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
    | true =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h2 (q : Pattern) (ha : d8285 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8286 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8286, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8287 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8288 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8246 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19784 q ha hb
    | true =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h7 (q : Pattern) (ha : d8292 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8293 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8293, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8294 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8295 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8296 q = 1) (hb : d116753 q = 1) : d120143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8296, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19796 (p : Pattern) (ha : d8363 p = 1) (hb : d116753 p = 1) : d120195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8239 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
    | true =>
      simp only [d8239, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h2 (q : Pattern) (ha : d8285 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8286 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8286, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8287 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8288 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8363 q = 1) (hb : d116753 q = 1) : d120195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8363, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19797 (p : Pattern) (ha : d8301 p = 1) (hb : d116753 p = 1) : d120148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8300 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8301 q = 1) (hb : d116753 q = 1) : d120148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19798 (p : Pattern) (ha : d8308 p = 1) (hb : d116753 p = 1) : d120155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8306 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8307 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8307, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8308 q = 1) (hb : d116753 q = 1) : d120155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19799 (p : Pattern) (ha : d138 p = 1) (hb : d116750 p = 1) : d750 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d137 q = 1) : d137 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d138 q = 1) (hb : d116750 q = 1) : d750 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d116750, d750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d138, d116750, d750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19800 (p : Pattern) (ha : d324 p = 1) (hb : d116752 p = 1) : d120159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d143 q = 1) (hb : d116750 q = 1) : d20892 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d324 q = 1) (hb : d116752 q = 1) : d120159 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324, d116752, d120159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324, d116752, d120159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19801 (p : Pattern) (ha : d8313 p = 1) (hb : d116753 p = 1) : d120165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d116752 q = 1) : d120160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19800 q ha hb
    | true =>
      simp only [d325, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19778 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d116752 q = 1) : d120161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d116752 q = 1) : d120162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d116753 q = 1) : d120163 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d116753, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d116753, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19778 q ha hb
    | true =>
      simp only [d145, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h7 (q : Pattern) (ha : d146 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d475, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8312 q = 1) (hb : d116753 q = 1) : d120164 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d120164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8312, d120164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8313 q = 1) (hb : d116753 q = 1) : d120165 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d120165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8313, d120165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19802 (p : Pattern) (ha : d8319 p = 1) (hb : d116753 p = 1) : d120171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d116753 q = 1) : d120169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d116753 q = 1) : d120170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8319 q = 1) (hb : d116753 q = 1) : d120171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d120171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d120171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19803 (p : Pattern) (ha : d8334 p = 1) (hb : d116753 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d116753 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19804 (p : Pattern) (ha : d94229 p = 1) (hb : d116753 p = 1) : d120177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8302 q = 1) (hb : d116753 q = 1) : d120149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19797 q ha hb
    | true =>
      simp only [d8302, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
  have h2 (q : Pattern) (ha : d8303 q = 1) (hb : d116753 q = 1) : d120150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8304 q = 1) (hb : d116753 q = 1) : d120151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8304, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8305 q = 1) (hb : d116753 q = 1) : d120152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8309 q = 1) (hb : d116753 q = 1) : d120156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19798 q ha hb
    | true =>
      simp only [d8309, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
  have h6 (q : Pattern) (ha : d8310 q = 1) (hb : d116753 q = 1) : d120157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8311 q = 1) (hb : d116753 q = 1) : d120158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8311, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8320 q = 1) (hb : d116753 q = 1) : d120172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19802 q ha hb
    | true =>
      simp only [d8320, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
  have h9 (q : Pattern) (ha : d94225 q = 1) (hb : d116753 q = 1) : d120173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94225, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8335 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19803 q ha hb
    | true =>
      simp only [d8335, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8336 q = 1) (hb : d116753 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8336, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94226 q = 1) (hb : d116753 q = 1) : d120174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94226, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94227 q = 1) (hb : d116753 q = 1) : d120175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94227, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94228 q = 1) (hb : d116753 q = 1) : d120176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94228, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94229 q = 1) (hb : d116753 q = 1) : d120177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d120177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d120177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19805 (p : Pattern) (ha : d8341 p = 1) (hb : d116753 p = 1) : d120178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8300 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8341 q = 1) (hb : d116753 q = 1) : d120178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8341, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19806 (p : Pattern) (ha : d8346 p = 1) (hb : d116753 p = 1) : d120183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8306 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8307 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8307, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8346 q = 1) (hb : d116753 q = 1) : d120183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8346, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19807 (p : Pattern) (ha : d8350 p = 1) (hb : d116753 p = 1) : d120187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d116753 q = 1) : d120169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d116753 q = 1) : d120170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8350 q = 1) (hb : d116753 q = 1) : d120187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d120187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8350, d120187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19808 (p : Pattern) (ha : d8355 p = 1) (hb : d116753 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19779 q ha hb
    | true =>
      simp only [d6740, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d116753 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19809 (p : Pattern) (ha : d94234 p = 1) (hb : d116753 p = 1) : d120193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8302 q = 1) (hb : d116753 q = 1) : d120149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19797 q ha hb
    | true =>
      simp only [d8302, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
  have h2 (q : Pattern) (ha : d8303 q = 1) (hb : d116753 q = 1) : d120150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8304 q = 1) (hb : d116753 q = 1) : d120151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8304, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8305 q = 1) (hb : d116753 q = 1) : d120152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8309 q = 1) (hb : d116753 q = 1) : d120156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19798 q ha hb
    | true =>
      simp only [d8309, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
  have h6 (q : Pattern) (ha : d8310 q = 1) (hb : d116753 q = 1) : d120157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8311 q = 1) (hb : d116753 q = 1) : d120158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8311, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8320 q = 1) (hb : d116753 q = 1) : d120172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19802 q ha hb
    | true =>
      simp only [d8320, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19780 q ha hb
  have h9 (q : Pattern) (ha : d94225 q = 1) (hb : d116753 q = 1) : d120173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94225, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8335 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19803 q ha hb
    | true =>
      simp only [d8335, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8336 q = 1) (hb : d116753 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8336, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94226 q = 1) (hb : d116753 q = 1) : d120174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94226, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94227 q = 1) (hb : d116753 q = 1) : d120175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94227, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94228 q = 1) (hb : d116753 q = 1) : d120176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94228, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8342 q = 1) (hb : d116753 q = 1) : d120179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19805 q ha hb
    | true =>
      simp only [d8342, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19782 q ha hb
  have h16 (q : Pattern) (ha : d8343 q = 1) (hb : d116753 q = 1) : d120180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8344 q = 1) (hb : d116753 q = 1) : d120181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8344, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8345 q = 1) (hb : d116753 q = 1) : d120182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8347 q = 1) (hb : d116753 q = 1) : d120184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19806 q ha hb
    | true =>
      simp only [d8347, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19783 q ha hb
  have h20 (q : Pattern) (ha : d8348 q = 1) (hb : d116753 q = 1) : d120185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8349 q = 1) (hb : d116753 q = 1) : d120186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8349, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8351 q = 1) (hb : d116753 q = 1) : d120188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19807 q ha hb
    | true =>
      simp only [d8351, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19784 q ha hb
  have h23 (q : Pattern) (ha : d94230 q = 1) (hb : d116753 q = 1) : d120189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94230, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8356 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19808 q ha hb
    | true =>
      simp only [d8356, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8357 q = 1) (hb : d116753 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8357, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94231 q = 1) (hb : d116753 q = 1) : d120190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94231, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94232 q = 1) (hb : d116753 q = 1) : d120191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d120191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94232, d120191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94233 q = 1) (hb : d116753 q = 1) : d120192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d120192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94233, d120192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94234 q = 1) (hb : d116753 q = 1) : d120193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d120193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94234, d120193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro19810 (p : Pattern) (ha : d94241 p = 1) (hb : d116753 p = 1) : d120202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d116753 q = 1) : d120188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19807 q ha hb
    | true =>
      simp only [d8351, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19784 q ha hb
  have h2 (q : Pattern) (ha : d94230 q = 1) (hb : d116753 q = 1) : d120189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94230, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8356 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19808 q ha hb
    | true =>
      simp only [d8356, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8357 q = 1) (hb : d116753 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8357, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d116753 q = 1) : d120190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d116753 q = 1) : d120200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d120200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d120200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d116753 q = 1) : d120201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d120201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d120201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d116753 q = 1) : d120202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d120202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d120202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19811 (p : Pattern) (ha : d417 p = 1) (hb : d116752 p = 1) : d120208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h3 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d230 q = 1) (hb : d116750 q = 1) : d20931 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d417 q = 1) (hb : d116752 q = 1) : d120208 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d116752, d120208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d417, d116752, d120208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19812 (p : Pattern) (ha : d8377 p = 1) (hb : d116753 p = 1) : d120214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d116752 q = 1) : d120209 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19811 q ha hb
    | true =>
      simp only [d418, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19787 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d116752 q = 1) : d120210 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d116752 q = 1) : d120211 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6843 q = 1) (hb : d116753 q = 1) : d120212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d116753, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d116753, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d232 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19787 q ha hb
    | true =>
      simp only [d232, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h7 (q : Pattern) (ha : d233 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d673, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8376 q = 1) (hb : d116753 q = 1) : d120213 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d120213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8376, d120213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8377 q = 1) (hb : d116753 q = 1) : d120214 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d120214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8377, d120214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19813 (p : Pattern) (ha : d8383 p = 1) (hb : d116753 p = 1) : d120220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d116753 q = 1) : d120215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19812 q ha hb
    | true =>
      simp only [d8378, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d116753 q = 1) : d120216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6773 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19788 q ha hb
    | true =>
      simp only [d6773, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6774 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8380 q = 1) (hb : d116753 q = 1) : d120217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d120217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8380, d120217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8381 q = 1) (hb : d116753 q = 1) : d120218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d120218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8381, d120218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8382 q = 1) (hb : d116753 q = 1) : d120219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d120219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8382, d120219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8383 q = 1) (hb : d116753 q = 1) : d120220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d120220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8383, d120220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19814 (p : Pattern) (ha : d8398 p = 1) (hb : d116753 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19788 q ha hb
    | true =>
      simp only [d6773, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d116753 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d116753 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d116753 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d116753 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19815 (p : Pattern) (ha : d94251 p = 1) (hb : d116753 p = 1) : d120226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d116753 q = 1) : d120221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19813 q ha hb
    | true =>
      simp only [d8384, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19789 q ha hb
  have h2 (q : Pattern) (ha : d94247 q = 1) (hb : d116753 q = 1) : d120222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d120222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94247, d120222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8399 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19814 q ha hb
    | true =>
      simp only [d8399, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8400 q = 1) (hb : d116753 q = 1) : d120116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8400, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d116753 q = 1) : d120223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d120223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d120223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d116753 q = 1) : d120224 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d120224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d120224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d116753 q = 1) : d120225 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d120225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d120225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d116753 q = 1) : d120226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d120226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d120226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19816 (p : Pattern) (ha : d94257 p = 1) (hb : d116753 p = 1) : d120232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d116753 q = 1) : d120137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19794 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d116753 q = 1) : d120138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d116753 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19794 q ha hb
    | true =>
      simp only [d8297, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19795 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d116753 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d116753 q = 1) : d120146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94235 q = 1) (hb : d116753 q = 1) : d120194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d120194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19804 q ha hb
    | true =>
      simp only [d94235, d120194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19809 q ha hb
  have h7 (q : Pattern) (ha : d8364 q = 1) (hb : d116753 q = 1) : d120196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19796 q ha hb
    | true =>
      simp only [d8364, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19774 q ha hb
  have h8 (q : Pattern) (ha : d94236 q = 1) (hb : d116753 q = 1) : d120197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d120197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d120197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94237 q = 1) (hb : d116753 q = 1) : d120198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d120198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94237, d120198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94238 q = 1) (hb : d116753 q = 1) : d120199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d120199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94238, d120199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94242 q = 1) (hb : d116753 q = 1) : d120203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d120203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94242, d120203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19810 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19792 q ha hb
  have h13 (q : Pattern) (ha : d94243 q = 1) (hb : d116753 q = 1) : d120204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d120204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94243, d120204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94244 q = 1) (hb : d116753 q = 1) : d120205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d120205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94244, d120205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94245 q = 1) (hb : d116753 q = 1) : d120206 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d120206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94245, d120206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94246 q = 1) (hb : d116753 q = 1) : d120207 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d120207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94246, d120207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94252 q = 1) (hb : d116753 q = 1) : d120227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d120227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94252, d120227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19815 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19793 q ha hb
  have h19 (q : Pattern) (ha : d94253 q = 1) (hb : d116753 q = 1) : d120228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d120228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94253, d120228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94254 q = 1) (hb : d116753 q = 1) : d120229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d120229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94254, d120229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94255 q = 1) (hb : d116753 q = 1) : d120230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d120230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94255, d120230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94256 q = 1) (hb : d116753 q = 1) : d120231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d120231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94256, d120231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94257 q = 1) (hb : d116753 q = 1) : d120232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d120232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94257, d120232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19817 (p : Pattern) (ha : d94263 p = 1) (hb : d116753 p = 1) : d120238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19772 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94220 q = 1) (hb : d116753 q = 1) : d120127 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94220, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19791 q ha hb
  have h6 (q : Pattern) (ha : d94221 q = 1) (hb : d116753 q = 1) : d120128 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94221, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94222 q = 1) (hb : d116753 q = 1) : d120129 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94222, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94223 q = 1) (hb : d116753 q = 1) : d120130 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94223, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94224 q = 1) (hb : d116753 q = 1) : d120131 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94224, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94258 q = 1) (hb : d116753 q = 1) : d120233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d120233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94258, d120233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19816 q ha hb
  have h11 (q : Pattern) (ha : d94259 q = 1) (hb : d116753 q = 1) : d120234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d120234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94259, d120234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94260 q = 1) (hb : d116753 q = 1) : d120235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d120235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94260, d120235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94261 q = 1) (hb : d116753 q = 1) : d120236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d120236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94261, d120236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94262 q = 1) (hb : d116753 q = 1) : d120237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d120237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94262, d120237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94263 q = 1) (hb : d116753 q = 1) : d120238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d120238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94263, d120238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19818 (p : Pattern) (ha : d481 p = 1) (hb : d116753 p = 1) : d120072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19778 q ha hb
    | true =>
      simp only [d145, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d480 q = 1) (hb : d116753 q = 1) : d120071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d481 q = 1) (hb : d116753 q = 1) : d120072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d481, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19819 (p : Pattern) (ha : d491 p = 1) (hb : d116753 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d116753 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19820 (p : Pattern) (ha : d501 p = 1) (hb : d116753 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d116753 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19821 (p : Pattern) (ha : d644 p = 1) (hb : d116753 p = 1) : d120143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19819 q ha hb
    | true =>
      simp only [d633, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19820 q ha hb
    | true =>
      simp only [d639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d116753 q = 1) : d120143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19822 (p : Pattern) (ha : d653 p = 1) (hb : d116753 p = 1) : d120334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19820 q ha hb
    | true =>
      simp only [d639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d116753 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19823 (p : Pattern) (ha : d683 p = 1) (hb : d116753 p = 1) : d120108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19787 q ha hb
    | true =>
      simp only [d232, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d682 q = 1) (hb : d116753 q = 1) : d120107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d683 q = 1) (hb : d116753 q = 1) : d120108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d683, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19824 (p : Pattern) (ha : d730 p = 1) (hb : d116753 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19823 q ha hb
    | true =>
      simp only [d684, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d116753 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d116753 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d116753 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d116753 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19825 (p : Pattern) (ha : d736 p = 1) (hb : d116753 p = 1) : d120378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19824 q ha hb
    | true =>
      simp only [d731, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d116753 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d116753 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d116753 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d116753 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d116753 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19826 (p : Pattern) (ha : d8420 p = 1) (hb : d116753 p = 1) : d120171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d116753 q = 1) : d120169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d116753 q = 1) : d120170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8420 q = 1) (hb : d116753 q = 1) : d120171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d120171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d120171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19827 (p : Pattern) (ha : d8426 p = 1) (hb : d116753 p = 1) : d120243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d116753 q = 1) : d120172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19826 q ha hb
    | true =>
      simp only [d8421, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19819 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d116753 q = 1) : d120239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d116753 q = 1) : d120240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d116753 q = 1) : d120241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d116753 q = 1) : d120242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8426 q = 1) (hb : d116753 q = 1) : d120243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d120243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d120243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19828 (p : Pattern) (ha : d8429 p = 1) (hb : d116753 p = 1) : d120187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d116753 q = 1) : d120169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d116753 q = 1) : d120170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8429 q = 1) (hb : d116753 q = 1) : d120187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d120187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8429, d120187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19829 (p : Pattern) (ha : d8435 p = 1) (hb : d116753 p = 1) : d120250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d116753 q = 1) : d120172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19826 q ha hb
    | true =>
      simp only [d8421, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19819 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d116753 q = 1) : d120239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d116753 q = 1) : d120240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d116753 q = 1) : d120241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d116753 q = 1) : d120242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8430 q = 1) (hb : d116753 q = 1) : d120188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19828 q ha hb
    | true =>
      simp only [d8430, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19820 q ha hb
  have h7 (q : Pattern) (ha : d8431 q = 1) (hb : d116753 q = 1) : d120246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8432 q = 1) (hb : d116753 q = 1) : d120247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8432, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8433 q = 1) (hb : d116753 q = 1) : d120248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8434 q = 1) (hb : d116753 q = 1) : d120249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8435 q = 1) (hb : d116753 q = 1) : d120250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d120250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8435, d120250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19830 (p : Pattern) (ha : d4818 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4818 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4818, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19831 (p : Pattern) (ha : d6799 p = 1) (hb : d116753 p = 1) : d120276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d116752 q = 1) : d120160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19800 q ha hb
    | true =>
      simp only [d325, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19778 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d116752 q = 1) : d120161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d116752 q = 1) : d120162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d116753 q = 1) : d120163 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d116753, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d116753, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4819 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19830 q ha hb
    | true =>
      simp only [d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h7 (q : Pattern) (ha : d4820 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4821 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4822 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4822, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6798 q = 1) (hb : d116753 q = 1) : d120275 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d120275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6798, d120275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6799 q = 1) (hb : d116753 q = 1) : d120276 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d120276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6799, d120276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19832 (p : Pattern) (ha : d8463 p = 1) (hb : d116753 p = 1) : d120286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d116753 q = 1) : d120277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19831 q ha hb
    | true =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d116753 q = 1) : d120278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d116753 q = 1) : d120283 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d116753 q = 1) : d120284 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d116753 q = 1) : d120285 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8463 q = 1) (hb : d116753 q = 1) : d120286 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d120286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d120286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19833 (p : Pattern) (ha : d8514 p = 1) (hb : d116753 p = 1) : d120325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8509 q = 1) (hb : d116753 q = 1) : d120320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8509, d120320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19832 q ha hb
    | true =>
      simp only [d8509, d120320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19819 q ha hb
  have h2 (q : Pattern) (ha : d8510 q = 1) (hb : d116753 q = 1) : d120321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8510, d120321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8510, d120321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8511 q = 1) (hb : d116753 q = 1) : d120322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8511, d120322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8511, d120322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8512 q = 1) (hb : d116753 q = 1) : d120323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8512, d120323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8512, d120323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8513 q = 1) (hb : d116753 q = 1) : d120324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8513, d120324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8513, d120324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19819 q ha hb
    | true =>
      simp only [d633, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8514 q = 1) (hb : d116753 q = 1) : d120325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8514, d120325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8514, d120325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19834 (p : Pattern) (ha : d514 p = 1) (hb : d116753 p = 1) : d120148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d116753 q = 1) : d120148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19835 (p : Pattern) (ha : d524 p = 1) (hb : d116753 p = 1) : d120155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d116753 q = 1) : d120155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19836 (p : Pattern) (ha : d8440 p = 1) (hb : d116753 p = 1) : d120255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d116753 q = 1) : d120169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8439 q = 1) (hb : d116753 q = 1) : d120254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8440 q = 1) (hb : d116753 q = 1) : d120255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8440, d120255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8440, d120255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19837 (p : Pattern) (ha : d8447 p = 1) (hb : d116753 p = 1) : d120262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8445 q = 1) (hb : d116753 q = 1) : d120260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8446 q = 1) (hb : d116753 q = 1) : d120261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8446, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8447 q = 1) (hb : d116753 q = 1) : d120262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8447, d120262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8447, d120262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19838 (p : Pattern) (ha : d318 p = 1) (hb : d116750 p = 1) : d20989 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d317 q = 1) : d317 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318 q = 1) (hb : d116750 q = 1) : d20989 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d116750, d20989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318, d116750, d20989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19839 (p : Pattern) (ha : d548 p = 1) (hb : d116752 p = 1) : d120266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d323 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d548 q = 1) (hb : d116752 q = 1) : d120266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d548, d116752, d120266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d548, d116752, d120266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19840 (p : Pattern) (ha : d8453 p = 1) (hb : d116753 p = 1) : d120272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d116752 q = 1) : d120267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d120267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19839 q ha hb
    | true =>
      simp only [d549, d120267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19800 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d116752 q = 1) : d120268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d120268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d120268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d116752 q = 1) : d120269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d120269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d120269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8451 q = 1) (hb : d116753 q = 1) : d120270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8451, d116753, d120270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8451, d116753, d120270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325 q = 1) (hb : d116752 q = 1) : d120160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19800 q ha hb
    | true =>
      simp only [d325, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19778 q ha hb
  have h7 (q : Pattern) (ha : d326 q = 1) (hb : d116752 q = 1) : d120161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d327 q = 1) (hb : d116752 q = 1) : d120162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6797 q = 1) (hb : d116753 q = 1) : d120163 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d116753, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6797, d116753, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8452 q = 1) (hb : d116753 q = 1) : d120271 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8452, d120271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8452, d120271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8453 q = 1) (hb : d116753 q = 1) : d120272 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8453, d120272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8453, d120272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19841 (p : Pattern) (ha : d8459 p = 1) (hb : d116753 p = 1) : d120282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d116753 q = 1) : d120273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19840 q ha hb
    | true =>
      simp only [d8454, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d116753 q = 1) : d120274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d116753 q = 1) : d120277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19831 q ha hb
    | true =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d116753 q = 1) : d120278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d116753 q = 1) : d120279 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d116753 q = 1) : d120280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d116753 q = 1) : d120281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8459 q = 1) (hb : d116753 q = 1) : d120282 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8459, d120282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8459, d120282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19842 (p : Pattern) (ha : d8479 p = 1) (hb : d116753 p = 1) : d120292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d116753 q = 1) : d120289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d116753 q = 1) : d120290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d116753 q = 1) : d120291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8479 q = 1) (hb : d116753 q = 1) : d120292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d120292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d120292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19843 (p : Pattern) (ha : d94268 p = 1) (hb : d116753 p = 1) : d120298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d116753 q = 1) : d120256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19836 q ha hb
    | true =>
      simp only [d8441, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19834 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d116753 q = 1) : d120257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d116753 q = 1) : d120258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d116753 q = 1) : d120259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d116753 q = 1) : d120263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19837 q ha hb
    | true =>
      simp only [d8448, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19835 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d116753 q = 1) : d120264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d116753 q = 1) : d120265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d116753 q = 1) : d120287 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19841 q ha hb
    | true =>
      simp only [d8464, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19832 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d116753 q = 1) : d120288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d116753 q = 1) : d120293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19842 q ha hb
    | true =>
      simp only [d8480, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d116753 q = 1) : d120294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d116753 q = 1) : d120295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d116753 q = 1) : d120296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d116753 q = 1) : d120297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94268 q = 1) (hb : d116753 q = 1) : d120298 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d120298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, d120298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19844 (p : Pattern) (ha : d610 p = 1) (hb : d116753 p = 1) : d120178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d116753 q = 1) : d120178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19845 (p : Pattern) (ha : d616 p = 1) (hb : d116753 p = 1) : d120183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d116753 q = 1) : d120183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19846 (p : Pattern) (ha : d8486 p = 1) (hb : d116753 p = 1) : d120299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d116753 q = 1) : d120169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8439 q = 1) (hb : d116753 q = 1) : d120254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8486 q = 1) (hb : d116753 q = 1) : d120299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8486, d120299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8486, d120299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19847 (p : Pattern) (ha : d8491 p = 1) (hb : d116753 p = 1) : d120304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d116753 q = 1) : d120168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8445 q = 1) (hb : d116753 q = 1) : d120260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8446 q = 1) (hb : d116753 q = 1) : d120261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8446, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8491 q = 1) (hb : d116753 q = 1) : d120304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8491, d120304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8491, d120304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19848 (p : Pattern) (ha : d8495 p = 1) (hb : d116753 p = 1) : d120308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d116753 q = 1) : d120273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19840 q ha hb
    | true =>
      simp only [d8454, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d116753 q = 1) : d120274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d116753 q = 1) : d120277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19831 q ha hb
    | true =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d116753 q = 1) : d120278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d116753 q = 1) : d120279 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d116753 q = 1) : d120280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d116753 q = 1) : d120281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8495 q = 1) (hb : d116753 q = 1) : d120308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8495, d120308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8495, d120308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19849 (p : Pattern) (ha : d8496 p = 1) (hb : d116753 p = 1) : d120309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d116753 q = 1) : d120277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19831 q ha hb
    | true =>
      simp only [d6800, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d116753 q = 1) : d120278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19818 q ha hb
    | true =>
      simp only [d482, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d116753 q = 1) : d120283 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d116753 q = 1) : d120284 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d116753 q = 1) : d120285 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8496 q = 1) (hb : d116753 q = 1) : d120309 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8496, d120309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8496, d120309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19850 (p : Pattern) (ha : d8501 p = 1) (hb : d116753 p = 1) : d120312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d116753 q = 1) : d120166 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19801 q ha hb
    | true =>
      simp only [d8314, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d116753 q = 1) : d120167 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d116753 q = 1) : d120289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d116753 q = 1) : d120290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d116753 q = 1) : d120291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8501 q = 1) (hb : d116753 q = 1) : d120312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d120312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8501, d120312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19851 (p : Pattern) (ha : d94273 p = 1) (hb : d116753 p = 1) : d120318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d116753 q = 1) : d120256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19836 q ha hb
    | true =>
      simp only [d8441, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19834 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d116753 q = 1) : d120257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d116753 q = 1) : d120258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d116753 q = 1) : d120259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d116753 q = 1) : d120263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19837 q ha hb
    | true =>
      simp only [d8448, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19835 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d116753 q = 1) : d120264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d116753 q = 1) : d120265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d116753 q = 1) : d120287 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19841 q ha hb
    | true =>
      simp only [d8464, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19832 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d116753 q = 1) : d120288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d116753 q = 1) : d120293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19842 q ha hb
    | true =>
      simp only [d8480, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d116753 q = 1) : d120294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d116753 q = 1) : d120295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d116753 q = 1) : d120296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d116753 q = 1) : d120297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8487 q = 1) (hb : d116753 q = 1) : d120300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8487, d120300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19846 q ha hb
    | true =>
      simp only [d8487, d120300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19844 q ha hb
  have h16 (q : Pattern) (ha : d8488 q = 1) (hb : d116753 q = 1) : d120301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8488, d120301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8488, d120301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8489 q = 1) (hb : d116753 q = 1) : d120302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8489, d120302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8489, d120302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8490 q = 1) (hb : d116753 q = 1) : d120303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8490, d120303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8490, d120303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8492 q = 1) (hb : d116753 q = 1) : d120305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8492, d120305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19847 q ha hb
    | true =>
      simp only [d8492, d120305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19845 q ha hb
  have h20 (q : Pattern) (ha : d8493 q = 1) (hb : d116753 q = 1) : d120306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8493, d120306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8493, d120306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8494 q = 1) (hb : d116753 q = 1) : d120307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8494, d120307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8494, d120307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8497 q = 1) (hb : d116753 q = 1) : d120310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19848 q ha hb
    | true =>
      simp only [d8497, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19849 q ha hb
  have h23 (q : Pattern) (ha : d94269 q = 1) (hb : d116753 q = 1) : d120311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94269, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8502 q = 1) (hb : d116753 q = 1) : d120313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19850 q ha hb
    | true =>
      simp only [d8502, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8503 q = 1) (hb : d116753 q = 1) : d120314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8503, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94270 q = 1) (hb : d116753 q = 1) : d120315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94270, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94271 q = 1) (hb : d116753 q = 1) : d120316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d120316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94271, d120316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94272 q = 1) (hb : d116753 q = 1) : d120317 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d120317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94272, d120317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94273 q = 1) (hb : d116753 q = 1) : d120318 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d120318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94273, d120318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro19852 (p : Pattern) (ha : d94280 p = 1) (hb : d116753 p = 1) : d120332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8497 q = 1) (hb : d116753 q = 1) : d120310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19848 q ha hb
    | true =>
      simp only [d8497, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19849 q ha hb
  have h2 (q : Pattern) (ha : d94269 q = 1) (hb : d116753 q = 1) : d120311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94269, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8502 q = 1) (hb : d116753 q = 1) : d120313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19850 q ha hb
    | true =>
      simp only [d8502, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8503 q = 1) (hb : d116753 q = 1) : d120314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8503, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d116753 q = 1) : d120315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94270, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d116753 q = 1) : d120330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d120330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, d120330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d116753 q = 1) : d120331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d120331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, d120331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d116753 q = 1) : d120332 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d120332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, d120332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19853 (p : Pattern) (ha : d6078 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d230 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6078 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6078, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19854 (p : Pattern) (ha : d6845 p = 1) (hb : d116753 p = 1) : d120350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d116752 q = 1) : d120209 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19811 q ha hb
    | true =>
      simp only [d418, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19787 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d116752 q = 1) : d120210 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d116752 q = 1) : d120211 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6843 q = 1) (hb : d116753 q = 1) : d120212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d116753, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d116753, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6079 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19853 q ha hb
    | true =>
      simp only [d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h7 (q : Pattern) (ha : d6080 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6081 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6082 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6082, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6844 q = 1) (hb : d116753 q = 1) : d120349 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6844, d120349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6844, d120349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6845 q = 1) (hb : d116753 q = 1) : d120350 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6845, d120350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6845, d120350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19855 (p : Pattern) (ha : d664 p = 1) (hb : d116752 p = 1) : d120340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h3 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h9 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d416 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d664 q = 1) (hb : d116752 q = 1) : d120340 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d116752, d120340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d664, d116752, d120340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19856 (p : Pattern) (ha : d8529 p = 1) (hb : d116753 p = 1) : d120346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d116752 q = 1) : d120341 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d120341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19855 q ha hb
    | true =>
      simp only [d665, d120341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19811 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d116752 q = 1) : d120342 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d120342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d120342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d116752 q = 1) : d120343 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d120343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d120343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8527 q = 1) (hb : d116753 q = 1) : d120344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8527, d116753, d120344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8527, d116753, d120344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d418 q = 1) (hb : d116752 q = 1) : d120209 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19811 q ha hb
    | true =>
      simp only [d418, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19787 q ha hb
  have h7 (q : Pattern) (ha : d419 q = 1) (hb : d116752 q = 1) : d120210 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d420 q = 1) (hb : d116752 q = 1) : d120211 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6843 q = 1) (hb : d116753 q = 1) : d120212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d116753, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6843, d116753, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8528 q = 1) (hb : d116753 q = 1) : d120345 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8528, d120345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8528, d120345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8529 q = 1) (hb : d116753 q = 1) : d120346 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8529, d120346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8529, d120346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19857 (p : Pattern) (ha : d8535 p = 1) (hb : d116753 p = 1) : d120356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8530 q = 1) (hb : d116753 q = 1) : d120347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8530, d120347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19856 q ha hb
    | true =>
      simp only [d8530, d120347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d116753 q = 1) : d120348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d120348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d120348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6846 q = 1) (hb : d116753 q = 1) : d120351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19854 q ha hb
    | true =>
      simp only [d6846, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6847 q = 1) (hb : d116753 q = 1) : d120352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8532 q = 1) (hb : d116753 q = 1) : d120353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8532, d120353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8532, d120353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8533 q = 1) (hb : d116753 q = 1) : d120354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8533, d120354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8533, d120354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8534 q = 1) (hb : d116753 q = 1) : d120355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8534, d120355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8534, d120355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8535 q = 1) (hb : d116753 q = 1) : d120356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8535, d120356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8535, d120356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19858 (p : Pattern) (ha : d8539 p = 1) (hb : d116753 p = 1) : d120360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6846 q = 1) (hb : d116753 q = 1) : d120351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19854 q ha hb
    | true =>
      simp only [d6846, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d116753 q = 1) : d120352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19823 q ha hb
    | true =>
      simp only [d684, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8536 q = 1) (hb : d116753 q = 1) : d120357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8536, d120357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8536, d120357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8537 q = 1) (hb : d116753 q = 1) : d120358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8537, d120358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8537, d120358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8538 q = 1) (hb : d116753 q = 1) : d120359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8538, d120359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8538, d120359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8539 q = 1) (hb : d116753 q = 1) : d120360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8539, d120360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8539, d120360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19859 (p : Pattern) (ha : d8555 p = 1) (hb : d116753 p = 1) : d120366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d116753 q = 1) : d120215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19812 q ha hb
    | true =>
      simp only [d8378, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d116753 q = 1) : d120216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8552 q = 1) (hb : d116753 q = 1) : d120363 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d120363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d120363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8553 q = 1) (hb : d116753 q = 1) : d120364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d120364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8553, d120364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8554 q = 1) (hb : d116753 q = 1) : d120365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d120365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8554, d120365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8555 q = 1) (hb : d116753 q = 1) : d120366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d120366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8555, d120366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19860 (p : Pattern) (ha : d94290 p = 1) (hb : d116753 p = 1) : d120372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8540 q = 1) (hb : d116753 q = 1) : d120361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8540, d120361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19857 q ha hb
    | true =>
      simp only [d8540, d120361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19858 q ha hb
  have h2 (q : Pattern) (ha : d94286 q = 1) (hb : d116753 q = 1) : d120362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d120362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94286, d120362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8556 q = 1) (hb : d116753 q = 1) : d120367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, d120367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19859 q ha hb
    | true =>
      simp only [d8556, d120367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8557 q = 1) (hb : d116753 q = 1) : d120368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, d120368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8557, d120368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d116753 q = 1) : d120369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d120369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94287, d120369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d116753 q = 1) : d120370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d120370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, d120370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d116753 q = 1) : d120371 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d120371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, d120371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d116753 q = 1) : d120372 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d120372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, d120372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19861 (p : Pattern) (ha : d94296 p = 1) (hb : d116753 p = 1) : d120384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8427 q = 1) (hb : d116753 q = 1) : d120244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8427, d120244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8427, d120244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19827 q ha hb
  have h2 (q : Pattern) (ha : d8428 q = 1) (hb : d116753 q = 1) : d120245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8428, d120245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8428, d120245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8436 q = 1) (hb : d116753 q = 1) : d120251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19827 q ha hb
    | true =>
      simp only [d8436, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19829 q ha hb
  have h4 (q : Pattern) (ha : d8437 q = 1) (hb : d116753 q = 1) : d120252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8437, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8438 q = 1) (hb : d116753 q = 1) : d120253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8438, d120253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8438, d120253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94274 q = 1) (hb : d116753 q = 1) : d120319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d120319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19843 q ha hb
    | true =>
      simp only [d94274, d120319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19851 q ha hb
  have h7 (q : Pattern) (ha : d8515 q = 1) (hb : d116753 q = 1) : d120326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8515, d120326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19833 q ha hb
    | true =>
      simp only [d8515, d120326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19821 q ha hb
  have h8 (q : Pattern) (ha : d94275 q = 1) (hb : d116753 q = 1) : d120327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d120327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94275, d120327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94276 q = 1) (hb : d116753 q = 1) : d120328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d120328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94276, d120328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94277 q = 1) (hb : d116753 q = 1) : d120329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d120329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94277, d120329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94281 q = 1) (hb : d116753 q = 1) : d120333 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d120333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94281, d120333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19852 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d116753 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19822 q ha hb
  have h13 (q : Pattern) (ha : d94282 q = 1) (hb : d116753 q = 1) : d120336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d120336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94282, d120336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94283 q = 1) (hb : d116753 q = 1) : d120337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d120337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94283, d120337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94284 q = 1) (hb : d116753 q = 1) : d120338 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d120338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94284, d120338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94285 q = 1) (hb : d116753 q = 1) : d120339 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d120339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94285, d120339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94291 q = 1) (hb : d116753 q = 1) : d120373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d120373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94291, d120373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19860 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d116753 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19825 q ha hb
  have h19 (q : Pattern) (ha : d94292 q = 1) (hb : d116753 q = 1) : d120380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d120380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94292, d120380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94293 q = 1) (hb : d116753 q = 1) : d120381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d120381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94293, d120381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94294 q = 1) (hb : d116753 q = 1) : d120382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d120382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94294, d120382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94295 q = 1) (hb : d116753 q = 1) : d120383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d120383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94295, d120383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94296 q = 1) (hb : d116753 q = 1) : d120384 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d120384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94296, d120384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19862 (p : Pattern) (ha : d94302 p = 1) (hb : d116753 p = 1) : d120390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d116753 q = 1) : d120385 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d120385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, d120385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19861 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d116753 q = 1) : d120386 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d120386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, d120386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d116753 q = 1) : d120387 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d120387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, d120387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d116753 q = 1) : d120388 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d120388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, d120388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d116753 q = 1) : d120389 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d120389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, d120389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d116753 q = 1) : d120390 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d120390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, d120390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19863 (p : Pattern) (ha : d758 p = 1) (hb : d116752 p = 1) : d120392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d757 q = 1) (hb : d116750 q = 1) : d757 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d758 q = 1) (hb : d116752 q = 1) : d120392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d116752, d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d758, d116752, d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19864 (p : Pattern) (ha : d762 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d762 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d762, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19865 (p : Pattern) (ha : d773 p = 1) (hb : d116753 p = 1) : d120406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d116752 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19863 q ha hb
    | true =>
      simp only [d763, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19864 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d116752 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d116752 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d767 q = 1) (hb : d116753 q = 1) : d120400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d772 q = 1) (hb : d116753 q = 1) : d120405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d772, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d773 q = 1) (hb : d116753 q = 1) : d120406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d773, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19866 (p : Pattern) (ha : d783 p = 1) (hb : d116753 p = 1) : d120416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d116753 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d116753 q = 1) : d120416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19867 (p : Pattern) (ha : d793 p = 1) (hb : d116753 p = 1) : d120426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d116753 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d116753 q = 1) : d120426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19868 (p : Pattern) (ha : d950 p = 1) (hb : d116753 p = 1) : d120525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d116753 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19866 q ha hb
    | true =>
      simp only [d939, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d116753 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d116753 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d116753 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d116753 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d116753 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19867 q ha hb
    | true =>
      simp only [d945, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d116753 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d116753 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d116753 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d116753 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d116753 q = 1) : d120525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19869 (p : Pattern) (ha : d959 p = 1) (hb : d116753 p = 1) : d120534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d116753 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19867 q ha hb
    | true =>
      simp only [d945, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d116753 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d116753 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d116753 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d116753 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d116753 q = 1) : d120534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19870 (p : Pattern) (ha : d981 p = 1) (hb : d116752 p = 1) : d120545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d980 q = 1) (hb : d116750 q = 1) : d980 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d981 q = 1) (hb : d116752 q = 1) : d120545 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d116752, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d981, d116752, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19871 (p : Pattern) (ha : d986 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d986 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d986, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19872 (p : Pattern) (ha : d1005 p = 1) (hb : d116753 p = 1) : d120567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d116752 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19870 q ha hb
    | true =>
      simp only [d987, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19871 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d116752 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d116752 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d116753 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1004 q = 1) (hb : d116753 q = 1) : d120566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1005 q = 1) (hb : d116753 q = 1) : d120567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1005, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19873 (p : Pattern) (ha : d1063 p = 1) (hb : d116753 p = 1) : d120594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d116753 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19872 q ha hb
    | true =>
      simp only [d1006, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d116753 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d116753 q = 1) : d120591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d116753 q = 1) : d120592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d116753 q = 1) : d120593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d116753 q = 1) : d120594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19874 (p : Pattern) (ha : d1069 p = 1) (hb : d116753 p = 1) : d120600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d116753 q = 1) : d120595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19873 q ha hb
    | true =>
      simp only [d1064, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d116753 q = 1) : d120596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d116753 q = 1) : d120597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d116753 q = 1) : d120598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d116753 q = 1) : d120599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d116753 q = 1) : d120600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19875 (p : Pattern) (ha : d756 p = 1) (hb : d116752 p = 1) : d120266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d755 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d756 q = 1) (hb : d116752 q = 1) : d120266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d756, d116752, d120266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d756, d116752, d120266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19876 (p : Pattern) (ha : d8576 p = 1) (hb : d116753 p = 1) : d120402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d116752 q = 1) : d120393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19875 q ha hb
    | true =>
      simp only [d759, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19863 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d116752 q = 1) : d120394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d116752 q = 1) : d120395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6875 q = 1) (hb : d116753 q = 1) : d120396 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d116753, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d116753, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d763 q = 1) (hb : d116752 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19863 q ha hb
    | true =>
      simp only [d763, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19864 q ha hb
  have h7 (q : Pattern) (ha : d764 q = 1) (hb : d116752 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d765 q = 1) (hb : d116752 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d767 q = 1) (hb : d116753 q = 1) : d120400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d767, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8575 q = 1) (hb : d116753 q = 1) : d120401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8575, d120401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8575, d120401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8576 q = 1) (hb : d116753 q = 1) : d120402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8576, d120402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8576, d120402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19877 (p : Pattern) (ha : d8582 p = 1) (hb : d116753 p = 1) : d120412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d116753 q = 1) : d120409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d116753 q = 1) : d120410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8581 q = 1) (hb : d116753 q = 1) : d120411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8581, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8582 q = 1) (hb : d116753 q = 1) : d120412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8582, d120412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8582, d120412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19878 (p : Pattern) (ha : d8588 p = 1) (hb : d116753 p = 1) : d120422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d116753 q = 1) : d120417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19877 q ha hb
    | true =>
      simp only [d8583, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19866 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d116753 q = 1) : d120418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d116753 q = 1) : d120419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d116753 q = 1) : d120420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d116753 q = 1) : d120421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8588 q = 1) (hb : d116753 q = 1) : d120422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d120422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d120422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19879 (p : Pattern) (ha : d8591 p = 1) (hb : d116753 p = 1) : d120425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d116753 q = 1) : d120409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d116753 q = 1) : d120410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8581 q = 1) (hb : d116753 q = 1) : d120411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8581, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8591 q = 1) (hb : d116753 q = 1) : d120425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8591, d120425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8591, d120425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19880 (p : Pattern) (ha : d8597 p = 1) (hb : d116753 p = 1) : d120432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d116753 q = 1) : d120417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19877 q ha hb
    | true =>
      simp only [d8583, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19866 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d116753 q = 1) : d120418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d116753 q = 1) : d120419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d116753 q = 1) : d120420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d116753 q = 1) : d120421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8592 q = 1) (hb : d116753 q = 1) : d120427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19879 q ha hb
    | true =>
      simp only [d8592, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19867 q ha hb
  have h7 (q : Pattern) (ha : d8593 q = 1) (hb : d116753 q = 1) : d120428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8594 q = 1) (hb : d116753 q = 1) : d120429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8594, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8595 q = 1) (hb : d116753 q = 1) : d120430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8596 q = 1) (hb : d116753 q = 1) : d120431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8597 q = 1) (hb : d116753 q = 1) : d120432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d120432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8597, d120432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19881 (p : Pattern) (ha : d4913 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4913 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4913, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19882 (p : Pattern) (ha : d6877 p = 1) (hb : d116753 p = 1) : d120463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d116752 q = 1) : d120393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19875 q ha hb
    | true =>
      simp only [d759, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19863 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d116752 q = 1) : d120394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d116752 q = 1) : d120395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6875 q = 1) (hb : d116753 q = 1) : d120396 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d116753, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d116753, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4914 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19881 q ha hb
    | true =>
      simp only [d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19864 q ha hb
  have h7 (q : Pattern) (ha : d4915 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4916 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4917 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4917, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6876 q = 1) (hb : d116753 q = 1) : d120462 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6876, d120462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6876, d120462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6877 q = 1) (hb : d116753 q = 1) : d120463 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6877, d120463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6877, d120463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19883 (p : Pattern) (ha : d8625 p = 1) (hb : d116753 p = 1) : d120473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d116753 q = 1) : d120464 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19882 q ha hb
    | true =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d116753 q = 1) : d120465 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d116753 q = 1) : d120470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d116753 q = 1) : d120471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d116753 q = 1) : d120472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8625 q = 1) (hb : d116753 q = 1) : d120473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8625, d120473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8625, d120473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19884 (p : Pattern) (ha : d8676 p = 1) (hb : d116753 p = 1) : d120519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8671 q = 1) (hb : d116753 q = 1) : d120509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8671, d120509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19883 q ha hb
    | true =>
      simp only [d8671, d120509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19866 q ha hb
  have h2 (q : Pattern) (ha : d8672 q = 1) (hb : d116753 q = 1) : d120510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8672, d120510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8672, d120510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8673 q = 1) (hb : d116753 q = 1) : d120511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8673, d120511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8673, d120511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8674 q = 1) (hb : d116753 q = 1) : d120512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8674, d120512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8674, d120512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8675 q = 1) (hb : d116753 q = 1) : d120513 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8675, d120513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8675, d120513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d116753 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19866 q ha hb
    | true =>
      simp only [d939, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d116753 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d116753 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d116753 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d116753 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8676 q = 1) (hb : d116753 q = 1) : d120519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8676, d120519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8676, d120519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19885 (p : Pattern) (ha : d806 p = 1) (hb : d116753 p = 1) : d120439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d116753 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d116753 q = 1) : d120439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19886 (p : Pattern) (ha : d816 p = 1) (hb : d116753 p = 1) : d120449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d116753 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d116753 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d116753 q = 1) : d120449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19887 (p : Pattern) (ha : d8602 p = 1) (hb : d116753 p = 1) : d120437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d116753 q = 1) : d120409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d116753 q = 1) : d120410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8601 q = 1) (hb : d116753 q = 1) : d120436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8602 q = 1) (hb : d116753 q = 1) : d120437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8602, d120437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8602, d120437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19888 (p : Pattern) (ha : d8609 p = 1) (hb : d116753 p = 1) : d120446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d116753 q = 1) : d120409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8607 q = 1) (hb : d116753 q = 1) : d120444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8608 q = 1) (hb : d116753 q = 1) : d120445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8608, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8609 q = 1) (hb : d116753 q = 1) : d120446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8609, d120446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8609, d120446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19889 (p : Pattern) (ha : d542 p = 1) (hb : d116750 p = 1) : d21182 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d541 q = 1) : d541 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d542 q = 1) (hb : d116750 q = 1) : d21182 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d542, d116750, d21182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d542, d116750, d21182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19890 (p : Pattern) (ha : d839 p = 1) (hb : d116752 p = 1) : d120453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d838 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d547 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d839 q = 1) (hb : d116752 q = 1) : d120453 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d839, d116752, d120453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d839, d116752, d120453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19891 (p : Pattern) (ha : d8615 p = 1) (hb : d116753 p = 1) : d120459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d116752 q = 1) : d120454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d120454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19890 q ha hb
    | true =>
      simp only [d840, d120454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19875 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d116752 q = 1) : d120455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d120455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d120455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d116752 q = 1) : d120456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d120456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d120456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8613 q = 1) (hb : d116753 q = 1) : d120457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8613, d116753, d120457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8613, d116753, d120457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d759 q = 1) (hb : d116752 q = 1) : d120393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19875 q ha hb
    | true =>
      simp only [d759, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19863 q ha hb
  have h7 (q : Pattern) (ha : d760 q = 1) (hb : d116752 q = 1) : d120394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d761 q = 1) (hb : d116752 q = 1) : d120395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6875 q = 1) (hb : d116753 q = 1) : d120396 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d116753, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6875, d116753, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8614 q = 1) (hb : d116753 q = 1) : d120458 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8614, d120458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8614, d120458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8615 q = 1) (hb : d116753 q = 1) : d120459 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8615, d120459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8615, d120459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19892 (p : Pattern) (ha : d8621 p = 1) (hb : d116753 p = 1) : d120469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d116753 q = 1) : d120460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19891 q ha hb
    | true =>
      simp only [d8616, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d116753 q = 1) : d120461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d116753 q = 1) : d120464 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19882 q ha hb
    | true =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d116753 q = 1) : d120465 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d116753 q = 1) : d120466 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d116753 q = 1) : d120467 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d116753 q = 1) : d120468 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8621 q = 1) (hb : d116753 q = 1) : d120469 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8621, d120469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8621, d120469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19893 (p : Pattern) (ha : d8641 p = 1) (hb : d116753 p = 1) : d120479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d116753 q = 1) : d120476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d116753 q = 1) : d120477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d116753 q = 1) : d120478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8641 q = 1) (hb : d116753 q = 1) : d120479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, d120479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, d120479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19894 (p : Pattern) (ha : d94308 p = 1) (hb : d116753 p = 1) : d120485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d116753 q = 1) : d120440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19887 q ha hb
    | true =>
      simp only [d8603, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19885 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d116753 q = 1) : d120441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d116753 q = 1) : d120442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d116753 q = 1) : d120443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d116753 q = 1) : d120450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19888 q ha hb
    | true =>
      simp only [d8610, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19886 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d116753 q = 1) : d120451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d116753 q = 1) : d120452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d116753 q = 1) : d120474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19892 q ha hb
    | true =>
      simp only [d8626, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19883 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d116753 q = 1) : d120475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d116753 q = 1) : d120480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19893 q ha hb
    | true =>
      simp only [d8642, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d116753 q = 1) : d120481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d116753 q = 1) : d120482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d116753 q = 1) : d120483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d116753 q = 1) : d120484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94308 q = 1) (hb : d116753 q = 1) : d120485 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d120485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, d120485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19895 (p : Pattern) (ha : d916 p = 1) (hb : d116753 p = 1) : d120487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d116753 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d116753 q = 1) : d120487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19896 (p : Pattern) (ha : d922 p = 1) (hb : d116753 p = 1) : d120493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d116753 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d116753 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d116753 q = 1) : d120493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19897 (p : Pattern) (ha : d8648 p = 1) (hb : d116753 p = 1) : d120486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d116753 q = 1) : d120409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d116753 q = 1) : d120410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8601 q = 1) (hb : d116753 q = 1) : d120436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8648 q = 1) (hb : d116753 q = 1) : d120486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8648, d120486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8648, d120486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19898 (p : Pattern) (ha : d8653 p = 1) (hb : d116753 p = 1) : d120492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d116753 q = 1) : d120409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8607 q = 1) (hb : d116753 q = 1) : d120444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8608 q = 1) (hb : d116753 q = 1) : d120445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8608, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8653 q = 1) (hb : d116753 q = 1) : d120492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8653, d120492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8653, d120492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19899 (p : Pattern) (ha : d8657 p = 1) (hb : d116753 p = 1) : d120497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d116753 q = 1) : d120460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19891 q ha hb
    | true =>
      simp only [d8616, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d116753 q = 1) : d120461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d116753 q = 1) : d120464 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19882 q ha hb
    | true =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d116753 q = 1) : d120465 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d116753 q = 1) : d120466 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d116753 q = 1) : d120467 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d116753 q = 1) : d120468 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8657 q = 1) (hb : d116753 q = 1) : d120497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8657, d120497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8657, d120497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19900 (p : Pattern) (ha : d8658 p = 1) (hb : d116753 p = 1) : d120498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d116753 q = 1) : d120464 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19882 q ha hb
    | true =>
      simp only [d6878, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d116753 q = 1) : d120465 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19865 q ha hb
    | true =>
      simp only [d774, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d116753 q = 1) : d120470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d116753 q = 1) : d120471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d116753 q = 1) : d120472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8658 q = 1) (hb : d116753 q = 1) : d120498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, d120498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8658, d120498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19901 (p : Pattern) (ha : d8663 p = 1) (hb : d116753 p = 1) : d120501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d116753 q = 1) : d120403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19876 q ha hb
    | true =>
      simp only [d8577, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d116753 q = 1) : d120404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d116753 q = 1) : d120476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d116753 q = 1) : d120477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d116753 q = 1) : d120478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8663 q = 1) (hb : d116753 q = 1) : d120501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d120501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8663, d120501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19902 (p : Pattern) (ha : d94313 p = 1) (hb : d116753 p = 1) : d120507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d116753 q = 1) : d120440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19887 q ha hb
    | true =>
      simp only [d8603, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19885 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d116753 q = 1) : d120441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d116753 q = 1) : d120442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d116753 q = 1) : d120443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d116753 q = 1) : d120450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19888 q ha hb
    | true =>
      simp only [d8610, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19886 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d116753 q = 1) : d120451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d116753 q = 1) : d120452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d116753 q = 1) : d120474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19892 q ha hb
    | true =>
      simp only [d8626, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19883 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d116753 q = 1) : d120475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d116753 q = 1) : d120480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19893 q ha hb
    | true =>
      simp only [d8642, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d116753 q = 1) : d120481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d116753 q = 1) : d120482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d116753 q = 1) : d120483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d116753 q = 1) : d120484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8649 q = 1) (hb : d116753 q = 1) : d120488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, d120488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19897 q ha hb
    | true =>
      simp only [d8649, d120488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19895 q ha hb
  have h16 (q : Pattern) (ha : d8650 q = 1) (hb : d116753 q = 1) : d120489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, d120489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, d120489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8651 q = 1) (hb : d116753 q = 1) : d120490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, d120490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8651, d120490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8652 q = 1) (hb : d116753 q = 1) : d120491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, d120491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, d120491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8654 q = 1) (hb : d116753 q = 1) : d120494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, d120494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19898 q ha hb
    | true =>
      simp only [d8654, d120494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19896 q ha hb
  have h20 (q : Pattern) (ha : d8655 q = 1) (hb : d116753 q = 1) : d120495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, d120495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, d120495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8656 q = 1) (hb : d116753 q = 1) : d120496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, d120496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8656, d120496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8659 q = 1) (hb : d116753 q = 1) : d120499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19899 q ha hb
    | true =>
      simp only [d8659, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19900 q ha hb
  have h23 (q : Pattern) (ha : d94309 q = 1) (hb : d116753 q = 1) : d120500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94309, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8664 q = 1) (hb : d116753 q = 1) : d120502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19901 q ha hb
    | true =>
      simp only [d8664, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8665 q = 1) (hb : d116753 q = 1) : d120503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8665, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94310 q = 1) (hb : d116753 q = 1) : d120504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94310, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94311 q = 1) (hb : d116753 q = 1) : d120505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d120505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94311, d120505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94312 q = 1) (hb : d116753 q = 1) : d120506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d120506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94312, d120506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94313 q = 1) (hb : d116753 q = 1) : d120507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d120507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94313, d120507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro19903 (p : Pattern) (ha : d94320 p = 1) (hb : d116753 p = 1) : d120532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d116753 q = 1) : d120499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19899 q ha hb
    | true =>
      simp only [d8659, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19900 q ha hb
  have h2 (q : Pattern) (ha : d94309 q = 1) (hb : d116753 q = 1) : d120500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94309, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8664 q = 1) (hb : d116753 q = 1) : d120502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19901 q ha hb
    | true =>
      simp only [d8664, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8665 q = 1) (hb : d116753 q = 1) : d120503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8665, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d116753 q = 1) : d120504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94310, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d116753 q = 1) : d120530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d120530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, d120530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d116753 q = 1) : d120531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d120531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, d120531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d116753 q = 1) : d120532 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d120532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, d120532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19904 (p : Pattern) (ha : d976 p = 1) (hb : d116752 p = 1) : d120340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h3 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d975 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d976 q = 1) (hb : d116752 q = 1) : d120340 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d116752, d120340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d976, d116752, d120340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19905 (p : Pattern) (ha : d6210 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6210 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6210, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19906 (p : Pattern) (ha : d6923 p = 1) (hb : d116753 p = 1) : d120555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d116752 q = 1) : d120546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19904 q ha hb
    | true =>
      simp only [d982, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19870 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d116752 q = 1) : d120547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d116752 q = 1) : d120548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d116753 q = 1) : d120549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d116753, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d116753, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6211 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19905 q ha hb
    | true =>
      simp only [d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19871 q ha hb
  have h7 (q : Pattern) (ha : d6212 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6213 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6214 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6214, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6922 q = 1) (hb : d116753 q = 1) : d120554 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, d120554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6922, d120554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6923 q = 1) (hb : d116753 q = 1) : d120555 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, d120555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6923, d120555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19907 (p : Pattern) (ha : d970 p = 1) (hb : d116752 p = 1) : d120540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h3 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h9 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d663 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d970 q = 1) (hb : d116752 q = 1) : d120540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d116752, d120540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d970, d116752, d120540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19908 (p : Pattern) (ha : d8691 p = 1) (hb : d116753 p = 1) : d120551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d116752 q = 1) : d120541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d120541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19907 q ha hb
    | true =>
      simp only [d977, d120541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19904 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d116752 q = 1) : d120542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d120542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d120542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d116752 q = 1) : d120543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d120543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d120543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8689 q = 1) (hb : d116753 q = 1) : d120544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d116753, d120544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8689, d116753, d120544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d982 q = 1) (hb : d116752 q = 1) : d120546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19904 q ha hb
    | true =>
      simp only [d982, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19870 q ha hb
  have h7 (q : Pattern) (ha : d983 q = 1) (hb : d116752 q = 1) : d120547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d984 q = 1) (hb : d116752 q = 1) : d120548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6921 q = 1) (hb : d116753 q = 1) : d120549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d116753, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6921, d116753, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8690 q = 1) (hb : d116753 q = 1) : d120550 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8690, d120550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8690, d120550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8691 q = 1) (hb : d116753 q = 1) : d120551 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8691, d120551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8691, d120551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19909 (p : Pattern) (ha : d8697 p = 1) (hb : d116753 p = 1) : d120561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d116753 q = 1) : d120552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d120552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19908 q ha hb
    | true =>
      simp only [d8692, d120552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d116753 q = 1) : d120553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d120553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d120553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6924 q = 1) (hb : d116753 q = 1) : d120556 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19906 q ha hb
    | true =>
      simp only [d6924, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d116753 q = 1) : d120557 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8694 q = 1) (hb : d116753 q = 1) : d120558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, d120558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8694, d120558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8695 q = 1) (hb : d116753 q = 1) : d120559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, d120559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8695, d120559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8696 q = 1) (hb : d116753 q = 1) : d120560 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, d120560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8696, d120560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8697 q = 1) (hb : d116753 q = 1) : d120561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, d120561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8697, d120561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19910 (p : Pattern) (ha : d8701 p = 1) (hb : d116753 p = 1) : d120573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d116753 q = 1) : d120556 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19906 q ha hb
    | true =>
      simp only [d6924, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d116753 q = 1) : d120557 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d116753 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19872 q ha hb
    | true =>
      simp only [d1006, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d116753 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8698 q = 1) (hb : d116753 q = 1) : d120570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, d120570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8698, d120570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8699 q = 1) (hb : d116753 q = 1) : d120571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, d120571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8699, d120571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8700 q = 1) (hb : d116753 q = 1) : d120572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, d120572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8700, d120572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8701 q = 1) (hb : d116753 q = 1) : d120573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, d120573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8701, d120573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19911 (p : Pattern) (ha : d8715 p = 1) (hb : d116753 p = 1) : d120577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d116752 q = 1) : d120546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19904 q ha hb
    | true =>
      simp only [d982, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19870 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d116752 q = 1) : d120547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d116752 q = 1) : d120548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d116753 q = 1) : d120549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d116753, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d116753, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d987 q = 1) (hb : d116752 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19870 q ha hb
    | true =>
      simp only [d987, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19871 q ha hb
  have h7 (q : Pattern) (ha : d988 q = 1) (hb : d116752 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d989 q = 1) (hb : d116752 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d116753 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d995, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8714 q = 1) (hb : d116753 q = 1) : d120576 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8714, d120576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8714, d120576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8715 q = 1) (hb : d116753 q = 1) : d120577 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8715, d120577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8715, d120577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19912 (p : Pattern) (ha : d8721 p = 1) (hb : d116753 p = 1) : d120583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d116753 q = 1) : d120578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19911 q ha hb
    | true =>
      simp only [d8716, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d116753 q = 1) : d120579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8718 q = 1) (hb : d116753 q = 1) : d120580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d120580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d120580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8719 q = 1) (hb : d116753 q = 1) : d120581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d120581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8719, d120581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8720 q = 1) (hb : d116753 q = 1) : d120582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d120582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8720, d120582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8721 q = 1) (hb : d116753 q = 1) : d120583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d120583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8721, d120583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19913 (p : Pattern) (ha : d94330 p = 1) (hb : d116753 p = 1) : d120589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d116753 q = 1) : d120574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, d120574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19909 q ha hb
    | true =>
      simp only [d8702, d120574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19910 q ha hb
  have h2 (q : Pattern) (ha : d94326 q = 1) (hb : d116753 q = 1) : d120575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d120575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94326, d120575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8722 q = 1) (hb : d116753 q = 1) : d120584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d120584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19912 q ha hb
    | true =>
      simp only [d8722, d120584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8723 q = 1) (hb : d116753 q = 1) : d120585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d120585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8723, d120585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d116753 q = 1) : d120586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d120586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94327, d120586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d116753 q = 1) : d120587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d120587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, d120587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d116753 q = 1) : d120588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d120588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, d120588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d116753 q = 1) : d120589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d120589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, d120589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19914 (p : Pattern) (ha : d94336 p = 1) (hb : d116753 p = 1) : d120606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d116753 q = 1) : d120423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, d120423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, d120423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19878 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d116753 q = 1) : d120424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, d120424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, d120424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d116753 q = 1) : d120433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19878 q ha hb
    | true =>
      simp only [d8598, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19880 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d116753 q = 1) : d120434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d116753 q = 1) : d120435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, d120435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, d120435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94314 q = 1) (hb : d116753 q = 1) : d120508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d120508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19894 q ha hb
    | true =>
      simp only [d94314, d120508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19902 q ha hb
  have h7 (q : Pattern) (ha : d8677 q = 1) (hb : d116753 q = 1) : d120526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, d120526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19884 q ha hb
    | true =>
      simp only [d8677, d120526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19868 q ha hb
  have h8 (q : Pattern) (ha : d94315 q = 1) (hb : d116753 q = 1) : d120527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d120527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94315, d120527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94316 q = 1) (hb : d116753 q = 1) : d120528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d120528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94316, d120528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94317 q = 1) (hb : d116753 q = 1) : d120529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d120529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94317, d120529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94321 q = 1) (hb : d116753 q = 1) : d120533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d120533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94321, d120533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19903 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d116753 q = 1) : d120535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19869 q ha hb
  have h13 (q : Pattern) (ha : d94322 q = 1) (hb : d116753 q = 1) : d120536 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d120536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94322, d120536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94323 q = 1) (hb : d116753 q = 1) : d120537 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d120537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94323, d120537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94324 q = 1) (hb : d116753 q = 1) : d120538 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d120538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94324, d120538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94325 q = 1) (hb : d116753 q = 1) : d120539 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d120539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94325, d120539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94331 q = 1) (hb : d116753 q = 1) : d120590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d120590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94331, d120590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19913 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d116753 q = 1) : d120601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19874 q ha hb
  have h19 (q : Pattern) (ha : d94332 q = 1) (hb : d116753 q = 1) : d120602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d120602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94332, d120602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94333 q = 1) (hb : d116753 q = 1) : d120603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d120603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94333, d120603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94334 q = 1) (hb : d116753 q = 1) : d120604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d120604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94334, d120604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94335 q = 1) (hb : d116753 q = 1) : d120605 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d120605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94335, d120605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94336 q = 1) (hb : d116753 q = 1) : d120606 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d120606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94336, d120606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19915 (p : Pattern) (ha : d94342 p = 1) (hb : d116753 p = 1) : d120612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d116753 q = 1) : d120607 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d120607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, d120607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19914 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d116753 q = 1) : d120608 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d120608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, d120608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d116753 q = 1) : d120609 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d120609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, d120609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d116753 q = 1) : d120610 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d120610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, d120610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d116753 q = 1) : d120611 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d120611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, d120611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d116753 q = 1) : d120612 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d120612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, d120612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19916 (p : Pattern) (ha : d1120 p = 1) (hb : d116750 p = 1) : d21754 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1108 q = 1) : d1108 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1120 q = 1) (hb : d116750 q = 1) : d21754 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1120, d116750, d21754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1120, d116750, d21754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19917 (p : Pattern) (ha : d1128 p = 1) (hb : d116752 p = 1) : d120616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1127 q = 1) (hb : d116750 q = 1) : d21776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1128 q = 1) (hb : d116752 q = 1) : d120616 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1128, d116752, d120616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1128, d116752, d120616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro19918 (p : Pattern) (ha : d1141 p = 1) (hb : d116752 p = 1) : d120621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1140 q = 1) (hb : d116750 q = 1) : d1140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1141 q = 1) (hb : d116752 q = 1) : d120621 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1141, d116752, d120621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1141, d116752, d120621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19919 (p : Pattern) (ha : d1152 p = 1) (hb : d116753 p = 1) : d120631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1142 q = 1) (hb : d116752 q = 1) : d120622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19917 q ha hb
    | true =>
      simp only [d1142, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19918 q ha hb
  have h2 (q : Pattern) (ha : d1143 q = 1) (hb : d116752 q = 1) : d120623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1144 q = 1) (hb : d116752 q = 1) : d120624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1146 q = 1) (hb : d116753 q = 1) : d120625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d116753, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1146, d116753, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1151 q = 1) (hb : d116753 q = 1) : d120630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d120630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1151, d120630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1152 q = 1) (hb : d116753 q = 1) : d120631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d120631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1152, d120631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19920 (p : Pattern) (ha : d1162 p = 1) (hb : d116753 p = 1) : d120641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d116753 q = 1) : d120638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d116753 q = 1) : d120639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d116753 q = 1) : d120640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d116753 q = 1) : d120641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d120641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d120641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19921 (p : Pattern) (ha : d1172 p = 1) (hb : d116753 p = 1) : d120651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d116753 q = 1) : d120638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d116753 q = 1) : d120639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d116753 q = 1) : d120640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d116753 q = 1) : d120651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d120651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d120651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19922 (p : Pattern) (ha : d1361 p = 1) (hb : d116753 p = 1) : d120750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d116753 q = 1) : d120739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19920 q ha hb
    | true =>
      simp only [d1350, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d116753 q = 1) : d120740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d116753 q = 1) : d120741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d116753 q = 1) : d120742 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d116753 q = 1) : d120743 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d116753 q = 1) : d120745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19921 q ha hb
    | true =>
      simp only [d1356, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d116753 q = 1) : d120746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d116753 q = 1) : d120747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d116753 q = 1) : d120748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d116753 q = 1) : d120749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d116753 q = 1) : d120750 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d120750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d120750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19923 (p : Pattern) (ha : d1370 p = 1) (hb : d116753 p = 1) : d120759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d116753 q = 1) : d120745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19921 q ha hb
    | true =>
      simp only [d1356, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d116753 q = 1) : d120746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d116753 q = 1) : d120747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d116753 q = 1) : d120748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d116753 q = 1) : d120749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d116753 q = 1) : d120759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d120759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d120759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19924 (p : Pattern) (ha : d1401 p = 1) (hb : d116752 p = 1) : d120771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1400 q = 1) (hb : d116750 q = 1) : d22096 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1401 q = 1) (hb : d116752 q = 1) : d120771 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d116752, d120771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1401, d116752, d120771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19925 (p : Pattern) (ha : d1411 p = 1) (hb : d116752 p = 1) : d120788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1400 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1410 q = 1) (hb : d116750 q = 1) : d1410 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1411 q = 1) (hb : d116752 q = 1) : d120788 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1411, d116752, d120788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1411, d116752, d120788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19926 (p : Pattern) (ha : d1430 p = 1) (hb : d116753 p = 1) : d120794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1412 q = 1) (hb : d116752 q = 1) : d120789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19924 q ha hb
    | true =>
      simp only [d1412, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19925 q ha hb
  have h2 (q : Pattern) (ha : d1413 q = 1) (hb : d116752 q = 1) : d120790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1414 q = 1) (hb : d116752 q = 1) : d120791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1420 q = 1) (hb : d116753 q = 1) : d120792 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d116753, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1420, d116753, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1429 q = 1) (hb : d116753 q = 1) : d120793 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d120793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1429, d120793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1430 q = 1) (hb : d116753 q = 1) : d120794 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d120794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1430, d120794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19927 (p : Pattern) (ha : d1497 p = 1) (hb : d116753 p = 1) : d120821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d116753 q = 1) : d120795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19926 q ha hb
    | true =>
      simp only [d1431, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d116753 q = 1) : d120796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d116753 q = 1) : d120818 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d120818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d120818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d116753 q = 1) : d120819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d120819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d120819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d116753 q = 1) : d120820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d120820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d120820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d116753 q = 1) : d120821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d120821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d120821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19928 (p : Pattern) (ha : d1503 p = 1) (hb : d116753 p = 1) : d120827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d116753 q = 1) : d120822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d120822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19927 q ha hb
    | true =>
      simp only [d1498, d120822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d116753 q = 1) : d120823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d120823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d120823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d116753 q = 1) : d120824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d120824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d120824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d116753 q = 1) : d120825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d120825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d120825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d116753 q = 1) : d120826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d120826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d120826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d116753 q = 1) : d120827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d120827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d120827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19929 (p : Pattern) (ha : d1109 p = 1) (hb : d116750 p = 1) : d21741 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1098 q = 1) : d1098 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1109 q = 1) (hb : d116750 q = 1) : d21741 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1109, d116750, d21741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1109, d116750, d21741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19930 (p : Pattern) (ha : d1126 p = 1) (hb : d116752 p = 1) : d120615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1125 q = 1) (hb : d116750 q = 1) : d21759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1126 q = 1) (hb : d116752 q = 1) : d120615 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1126, d116752, d120615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1126, d116752, d120615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19931 (p : Pattern) (ha : d8743 p = 1) (hb : d116753 p = 1) : d120627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d116752 q = 1) : d120617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19930 q ha hb
    | true =>
      simp only [d1129, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19917 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d116752 q = 1) : d120618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d116752 q = 1) : d120619 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d116753 q = 1) : d120620 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d116753, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d116753, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1142 q = 1) (hb : d116752 q = 1) : d120622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19917 q ha hb
    | true =>
      simp only [d1142, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19918 q ha hb
  have h7 (q : Pattern) (ha : d1143 q = 1) (hb : d116752 q = 1) : d120623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1144 q = 1) (hb : d116752 q = 1) : d120624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1146 q = 1) (hb : d116753 q = 1) : d120625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d116753, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1146, d116753, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8742 q = 1) (hb : d116753 q = 1) : d120626 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8742, d120626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8742, d120626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8743 q = 1) (hb : d116753 q = 1) : d120627 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8743, d120627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8743, d120627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19932 (p : Pattern) (ha : d8749 p = 1) (hb : d116753 p = 1) : d120637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d116753 q = 1) : d120634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d116753 q = 1) : d120635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d116753 q = 1) : d120636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8749 q = 1) (hb : d116753 q = 1) : d120637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, d120637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, d120637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19933 (p : Pattern) (ha : d8755 p = 1) (hb : d116753 p = 1) : d120647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d116753 q = 1) : d120642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19932 q ha hb
    | true =>
      simp only [d8750, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19920 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d116753 q = 1) : d120643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d116753 q = 1) : d120644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d116753 q = 1) : d120645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d116753 q = 1) : d120646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8755 q = 1) (hb : d116753 q = 1) : d120647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d120647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d120647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19934 (p : Pattern) (ha : d8758 p = 1) (hb : d116753 p = 1) : d120650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d116753 q = 1) : d120634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d116753 q = 1) : d120635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d116753 q = 1) : d120636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8758 q = 1) (hb : d116753 q = 1) : d120650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, d120650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8758, d120650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19935 (p : Pattern) (ha : d8764 p = 1) (hb : d116753 p = 1) : d120657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d116753 q = 1) : d120642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19932 q ha hb
    | true =>
      simp only [d8750, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19920 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d116753 q = 1) : d120643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d116753 q = 1) : d120644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d116753 q = 1) : d120645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d116753 q = 1) : d120646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8759 q = 1) (hb : d116753 q = 1) : d120652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19934 q ha hb
    | true =>
      simp only [d8759, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19921 q ha hb
  have h7 (q : Pattern) (ha : d8760 q = 1) (hb : d116753 q = 1) : d120653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8761 q = 1) (hb : d116753 q = 1) : d120654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8761, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8762 q = 1) (hb : d116753 q = 1) : d120655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8763 q = 1) (hb : d116753 q = 1) : d120656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8764 q = 1) (hb : d116753 q = 1) : d120657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d120657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8764, d120657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19936 (p : Pattern) (ha : d5009 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5009 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5009, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19937 (p : Pattern) (ha : d5023 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5023 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5023, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5023, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19938 (p : Pattern) (ha : d6956 p = 1) (hb : d116753 p = 1) : d120688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d116752 q = 1) : d120617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19930 q ha hb
    | true =>
      simp only [d1129, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19917 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d116752 q = 1) : d120618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d116752 q = 1) : d120619 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d116753 q = 1) : d120620 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d116753, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d116753, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5024 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19936 q ha hb
    | true =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19937 q ha hb
  have h7 (q : Pattern) (ha : d5025 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5026 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5027 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5027, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d6955 q = 1) (hb : d116753 q = 1) : d120687 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, d120687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6955, d120687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6956 q = 1) (hb : d116753 q = 1) : d120688 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, d120688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6956, d120688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19939 (p : Pattern) (ha : d8792 p = 1) (hb : d116753 p = 1) : d120698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d116753 q = 1) : d120689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19938 q ha hb
    | true =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d116753 q = 1) : d120690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d116753 q = 1) : d120695 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d116753 q = 1) : d120696 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d116753 q = 1) : d120697 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8792 q = 1) (hb : d116753 q = 1) : d120698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, d120698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, d120698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19940 (p : Pattern) (ha : d8843 p = 1) (hb : d116753 p = 1) : d120744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8838 q = 1) (hb : d116753 q = 1) : d120734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, d120734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19939 q ha hb
    | true =>
      simp only [d8838, d120734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19920 q ha hb
  have h2 (q : Pattern) (ha : d8839 q = 1) (hb : d116753 q = 1) : d120735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, d120735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, d120735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8840 q = 1) (hb : d116753 q = 1) : d120736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, d120736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8840, d120736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8841 q = 1) (hb : d116753 q = 1) : d120737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, d120737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, d120737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8842 q = 1) (hb : d116753 q = 1) : d120738 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, d120738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, d120738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d116753 q = 1) : d120739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19920 q ha hb
    | true =>
      simp only [d1350, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d116753 q = 1) : d120740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d116753 q = 1) : d120741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d116753 q = 1) : d120742 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d116753 q = 1) : d120743 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8843 q = 1) (hb : d116753 q = 1) : d120744 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, d120744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8843, d120744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19941 (p : Pattern) (ha : d1185 p = 1) (hb : d116753 p = 1) : d120664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d116753 q = 1) : d120638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d116753 q = 1) : d120639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d116753 q = 1) : d120663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d116753 q = 1) : d120664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d120664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d120664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19942 (p : Pattern) (ha : d1195 p = 1) (hb : d116753 p = 1) : d120674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d116753 q = 1) : d120638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d116753 q = 1) : d120672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d116753 q = 1) : d120673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d116753 q = 1) : d120674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d120674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d120674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19943 (p : Pattern) (ha : d8769 p = 1) (hb : d116753 p = 1) : d120662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d116753 q = 1) : d120634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d116753 q = 1) : d120635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d116753 q = 1) : d120661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8769 q = 1) (hb : d116753 q = 1) : d120662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, d120662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, d120662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19944 (p : Pattern) (ha : d8776 p = 1) (hb : d116753 p = 1) : d120671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d116753 q = 1) : d120634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d116753 q = 1) : d120669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d116753 q = 1) : d120670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8776 q = 1) (hb : d116753 q = 1) : d120671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, d120671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, d120671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19945 (p : Pattern) (ha : d1099 p = 1) (hb : d116750 p = 1) : d21736 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1092 q = 1) : d1092 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1099 q = 1) (hb : d116750 q = 1) : d21736 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1099, d116750, d21736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1099, d116750, d21736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19946 (p : Pattern) (ha : d1215 p = 1) (hb : d116752 p = 1) : d120678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1114 q = 1) (hb : d116750 q = 1) : d21746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1114, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1215 q = 1) (hb : d116752 q = 1) : d120678 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1215, d116752, d120678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1215, d116752, d120678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19947 (p : Pattern) (ha : d8782 p = 1) (hb : d116753 p = 1) : d120684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d116752 q = 1) : d120679 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d120679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19946 q ha hb
    | true =>
      simp only [d1216, d120679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19930 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d116752 q = 1) : d120680 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d120680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d120680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d116752 q = 1) : d120681 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d120681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d120681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8780 q = 1) (hb : d116753 q = 1) : d120682 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d116753, d120682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8780, d116753, d120682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1129 q = 1) (hb : d116752 q = 1) : d120617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19930 q ha hb
    | true =>
      simp only [d1129, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19917 q ha hb
  have h7 (q : Pattern) (ha : d1130 q = 1) (hb : d116752 q = 1) : d120618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1131 q = 1) (hb : d116752 q = 1) : d120619 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6954 q = 1) (hb : d116753 q = 1) : d120620 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d116753, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6954, d116753, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8781 q = 1) (hb : d116753 q = 1) : d120683 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8781, d120683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8781, d120683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8782 q = 1) (hb : d116753 q = 1) : d120684 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8782, d120684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8782, d120684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19948 (p : Pattern) (ha : d8788 p = 1) (hb : d116753 p = 1) : d120694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d116753 q = 1) : d120685 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19947 q ha hb
    | true =>
      simp only [d8783, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d116753 q = 1) : d120686 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d116753 q = 1) : d120689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19938 q ha hb
    | true =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d116753 q = 1) : d120690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d116753 q = 1) : d120691 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d116753 q = 1) : d120692 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d116753 q = 1) : d120693 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8788 q = 1) (hb : d116753 q = 1) : d120694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, d120694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, d120694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19949 (p : Pattern) (ha : d8808 p = 1) (hb : d116753 p = 1) : d120704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d116753 q = 1) : d120701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d116753 q = 1) : d120702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d116753 q = 1) : d120703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8808 q = 1) (hb : d116753 q = 1) : d120704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d120704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d120704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19950 (p : Pattern) (ha : d94349 p = 1) (hb : d116753 p = 1) : d120710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d116753 q = 1) : d120665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19943 q ha hb
    | true =>
      simp only [d8770, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19941 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d116753 q = 1) : d120666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d116753 q = 1) : d120667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d116753 q = 1) : d120668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d116753 q = 1) : d120675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19944 q ha hb
    | true =>
      simp only [d8777, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19942 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d116753 q = 1) : d120676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d116753 q = 1) : d120677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d116753 q = 1) : d120699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19948 q ha hb
    | true =>
      simp only [d8793, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19939 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d116753 q = 1) : d120700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d116753 q = 1) : d120705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19949 q ha hb
    | true =>
      simp only [d8809, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d116753 q = 1) : d120706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d116753 q = 1) : d120707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d116753 q = 1) : d120708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d116753 q = 1) : d120709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94349 q = 1) (hb : d116753 q = 1) : d120710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d120710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, d120710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19951 (p : Pattern) (ha : d1327 p = 1) (hb : d116753 p = 1) : d120712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d116753 q = 1) : d120638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d116753 q = 1) : d120639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d116753 q = 1) : d120663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d116753 q = 1) : d120712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d120712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d120712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19952 (p : Pattern) (ha : d1333 p = 1) (hb : d116753 p = 1) : d120718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d116753 q = 1) : d120638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d116753 q = 1) : d120672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d116753 q = 1) : d120673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d116753 q = 1) : d120718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d120718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d120718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19953 (p : Pattern) (ha : d8815 p = 1) (hb : d116753 p = 1) : d120711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d116753 q = 1) : d120634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d116753 q = 1) : d120635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d116753 q = 1) : d120661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8815 q = 1) (hb : d116753 q = 1) : d120711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, d120711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8815, d120711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19954 (p : Pattern) (ha : d8820 p = 1) (hb : d116753 p = 1) : d120717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d116753 q = 1) : d120634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d116753 q = 1) : d120669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d116753 q = 1) : d120670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8820 q = 1) (hb : d116753 q = 1) : d120717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, d120717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8820, d120717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19955 (p : Pattern) (ha : d8824 p = 1) (hb : d116753 p = 1) : d120722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d116753 q = 1) : d120685 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19947 q ha hb
    | true =>
      simp only [d8783, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d116753 q = 1) : d120686 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d116753 q = 1) : d120689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19938 q ha hb
    | true =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d116753 q = 1) : d120690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d116753 q = 1) : d120691 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d116753 q = 1) : d120692 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d116753 q = 1) : d120693 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8824 q = 1) (hb : d116753 q = 1) : d120722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, d120722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8824, d120722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19956 (p : Pattern) (ha : d8825 p = 1) (hb : d116753 p = 1) : d120723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d116753 q = 1) : d120689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19938 q ha hb
    | true =>
      simp only [d6957, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d116753 q = 1) : d120690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d116753 q = 1) : d120632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19919 q ha hb
    | true =>
      simp only [d1153, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d116753 q = 1) : d120633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d116753 q = 1) : d120695 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d116753 q = 1) : d120696 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d116753 q = 1) : d120697 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8825 q = 1) (hb : d116753 q = 1) : d120723 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, d120723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8825, d120723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19957 (p : Pattern) (ha : d8830 p = 1) (hb : d116753 p = 1) : d120726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d116753 q = 1) : d120628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19931 q ha hb
    | true =>
      simp only [d8744, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d116753 q = 1) : d120629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d116753 q = 1) : d120701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d116753 q = 1) : d120702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d116753 q = 1) : d120703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8830 q = 1) (hb : d116753 q = 1) : d120726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d120726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8830, d120726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19958 (p : Pattern) (ha : d94354 p = 1) (hb : d116753 p = 1) : d120732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d116753 q = 1) : d120665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19943 q ha hb
    | true =>
      simp only [d8770, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19941 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d116753 q = 1) : d120666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d116753 q = 1) : d120667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d116753 q = 1) : d120668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d116753 q = 1) : d120675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19944 q ha hb
    | true =>
      simp only [d8777, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19942 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d116753 q = 1) : d120676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d116753 q = 1) : d120677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d116753 q = 1) : d120699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19948 q ha hb
    | true =>
      simp only [d8793, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19939 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d116753 q = 1) : d120700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d116753 q = 1) : d120705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19949 q ha hb
    | true =>
      simp only [d8809, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d116753 q = 1) : d120706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d116753 q = 1) : d120707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d116753 q = 1) : d120708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d116753 q = 1) : d120709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8816 q = 1) (hb : d116753 q = 1) : d120713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, d120713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19953 q ha hb
    | true =>
      simp only [d8816, d120713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19951 q ha hb
  have h16 (q : Pattern) (ha : d8817 q = 1) (hb : d116753 q = 1) : d120714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, d120714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, d120714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8818 q = 1) (hb : d116753 q = 1) : d120715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, d120715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8818, d120715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8819 q = 1) (hb : d116753 q = 1) : d120716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, d120716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, d120716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8821 q = 1) (hb : d116753 q = 1) : d120719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, d120719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19954 q ha hb
    | true =>
      simp only [d8821, d120719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19952 q ha hb
  have h20 (q : Pattern) (ha : d8822 q = 1) (hb : d116753 q = 1) : d120720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, d120720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, d120720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8823 q = 1) (hb : d116753 q = 1) : d120721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, d120721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8823, d120721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8826 q = 1) (hb : d116753 q = 1) : d120724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19955 q ha hb
    | true =>
      simp only [d8826, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19956 q ha hb
  have h23 (q : Pattern) (ha : d94350 q = 1) (hb : d116753 q = 1) : d120725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94350, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8831 q = 1) (hb : d116753 q = 1) : d120727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19957 q ha hb
    | true =>
      simp only [d8831, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8832 q = 1) (hb : d116753 q = 1) : d120728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8832, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94351 q = 1) (hb : d116753 q = 1) : d120729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94351, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94352 q = 1) (hb : d116753 q = 1) : d120730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d120730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94352, d120730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94353 q = 1) (hb : d116753 q = 1) : d120731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d120731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94353, d120731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94354 q = 1) (hb : d116753 q = 1) : d120732 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d120732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94354, d120732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro19959 (p : Pattern) (ha : d94361 p = 1) (hb : d116753 p = 1) : d120757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d116753 q = 1) : d120724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19955 q ha hb
    | true =>
      simp only [d8826, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19956 q ha hb
  have h2 (q : Pattern) (ha : d94350 q = 1) (hb : d116753 q = 1) : d120725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94350, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8831 q = 1) (hb : d116753 q = 1) : d120727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19957 q ha hb
    | true =>
      simp only [d8831, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8832 q = 1) (hb : d116753 q = 1) : d120728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8832, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d116753 q = 1) : d120729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94351, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d116753 q = 1) : d120755 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d120755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, d120755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d116753 q = 1) : d120756 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d120756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, d120756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d116753 q = 1) : d120757 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d120757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, d120757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19960 (p : Pattern) (ha : d1396 p = 1) (hb : d116752 p = 1) : d120766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h3 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h9 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1395 q = 1) (hb : d116750 q = 1) : d22068 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1396 q = 1) (hb : d116752 q = 1) : d120766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d116752, d120766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1396, d116752, d120766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19961 (p : Pattern) (ha : d6349 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6349 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6349, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19962 (p : Pattern) (ha : d6355 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6355 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6355, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19963 (p : Pattern) (ha : d7002 p = 1) (hb : d116753 p = 1) : d120781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d116752 q = 1) : d120772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19960 q ha hb
    | true =>
      simp only [d1402, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19924 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d116752 q = 1) : d120773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d116752 q = 1) : d120774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d116753 q = 1) : d120775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d116753, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d116753, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6356 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19961 q ha hb
    | true =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19962 q ha hb
  have h7 (q : Pattern) (ha : d6357 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6358 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6359 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6359, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d7001 q = 1) (hb : d116753 q = 1) : d120780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, d120780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7001, d120780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7002 q = 1) (hb : d116753 q = 1) : d120781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, d120781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7002, d120781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19964 (p : Pattern) (ha : d1390 p = 1) (hb : d116752 p = 1) : d120765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1384 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h3 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h9 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1389 q = 1) (hb : d116750 q = 1) : d22047 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1389, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1390 q = 1) (hb : d116752 q = 1) : d120765 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d116752, d120765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1390, d116752, d120765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro19965 (p : Pattern) (ha : d8858 p = 1) (hb : d116753 p = 1) : d120777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d116752 q = 1) : d120767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d120767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19964 q ha hb
    | true =>
      simp only [d1397, d120767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19960 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d116752 q = 1) : d120768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d120768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d120768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d116752 q = 1) : d120769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d120769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d120769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8856 q = 1) (hb : d116753 q = 1) : d120770 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d116753, d120770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8856, d116753, d120770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1402 q = 1) (hb : d116752 q = 1) : d120772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19960 q ha hb
    | true =>
      simp only [d1402, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19924 q ha hb
  have h7 (q : Pattern) (ha : d1403 q = 1) (hb : d116752 q = 1) : d120773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1404 q = 1) (hb : d116752 q = 1) : d120774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7000 q = 1) (hb : d116753 q = 1) : d120775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d116753, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7000, d116753, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8857 q = 1) (hb : d116753 q = 1) : d120776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8857, d120776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8857, d120776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8858 q = 1) (hb : d116753 q = 1) : d120777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8858, d120777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8858, d120777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19966 (p : Pattern) (ha : d8864 p = 1) (hb : d116753 p = 1) : d120787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d116753 q = 1) : d120778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d120778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19965 q ha hb
    | true =>
      simp only [d8859, d120778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d116753 q = 1) : d120779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d120779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d120779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7003 q = 1) (hb : d116753 q = 1) : d120782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19963 q ha hb
    | true =>
      simp only [d7003, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d116753 q = 1) : d120783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8861 q = 1) (hb : d116753 q = 1) : d120784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, d120784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8861, d120784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8862 q = 1) (hb : d116753 q = 1) : d120785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, d120785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8862, d120785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8863 q = 1) (hb : d116753 q = 1) : d120786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, d120786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8863, d120786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8864 q = 1) (hb : d116753 q = 1) : d120787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, d120787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8864, d120787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19967 (p : Pattern) (ha : d8868 p = 1) (hb : d116753 p = 1) : d120800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d116753 q = 1) : d120782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19963 q ha hb
    | true =>
      simp only [d7003, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d116753 q = 1) : d120783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d116753 q = 1) : d120795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19926 q ha hb
    | true =>
      simp only [d1431, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d116753 q = 1) : d120796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8865 q = 1) (hb : d116753 q = 1) : d120797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, d120797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8865, d120797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8866 q = 1) (hb : d116753 q = 1) : d120798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, d120798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8866, d120798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8867 q = 1) (hb : d116753 q = 1) : d120799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, d120799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8867, d120799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8868 q = 1) (hb : d116753 q = 1) : d120800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, d120800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8868, d120800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19968 (p : Pattern) (ha : d8882 p = 1) (hb : d116753 p = 1) : d120804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d116752 q = 1) : d120772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19960 q ha hb
    | true =>
      simp only [d1402, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19924 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d116752 q = 1) : d120773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d116752 q = 1) : d120774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d116753 q = 1) : d120775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d116753, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d116753, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1412 q = 1) (hb : d116752 q = 1) : d120789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19924 q ha hb
    | true =>
      simp only [d1412, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19925 q ha hb
  have h7 (q : Pattern) (ha : d1413 q = 1) (hb : d116752 q = 1) : d120790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1414 q = 1) (hb : d116752 q = 1) : d120791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1420 q = 1) (hb : d116753 q = 1) : d120792 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d116753, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1420, d116753, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8881 q = 1) (hb : d116753 q = 1) : d120803 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, d120803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8881, d120803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8882 q = 1) (hb : d116753 q = 1) : d120804 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, d120804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8882, d120804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19969 (p : Pattern) (ha : d8888 p = 1) (hb : d116753 p = 1) : d120810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d116753 q = 1) : d120805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19968 q ha hb
    | true =>
      simp only [d8883, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d116753 q = 1) : d120806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8885 q = 1) (hb : d116753 q = 1) : d120807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d120807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d120807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8886 q = 1) (hb : d116753 q = 1) : d120808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d120808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8886, d120808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8887 q = 1) (hb : d116753 q = 1) : d120809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d120809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8887, d120809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8888 q = 1) (hb : d116753 q = 1) : d120810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d120810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8888, d120810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19970 (p : Pattern) (ha : d94371 p = 1) (hb : d116753 p = 1) : d120816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d116753 q = 1) : d120801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, d120801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19966 q ha hb
    | true =>
      simp only [d8869, d120801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19967 q ha hb
  have h2 (q : Pattern) (ha : d94367 q = 1) (hb : d116753 q = 1) : d120802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d120802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94367, d120802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8889 q = 1) (hb : d116753 q = 1) : d120811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d120811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19969 q ha hb
    | true =>
      simp only [d8889, d120811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8890 q = 1) (hb : d116753 q = 1) : d120812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d120812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8890, d120812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d116753 q = 1) : d120813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d120813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94368, d120813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d116753 q = 1) : d120814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d120814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, d120814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d116753 q = 1) : d120815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d120815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, d120815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d116753 q = 1) : d120816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d120816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, d120816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19971 (p : Pattern) (ha : d94377 p = 1) (hb : d116753 p = 1) : d120833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d116753 q = 1) : d120648 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, d120648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, d120648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19933 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d116753 q = 1) : d120649 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, d120649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, d120649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d116753 q = 1) : d120658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19933 q ha hb
    | true =>
      simp only [d8765, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19935 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d116753 q = 1) : d120659 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d116753 q = 1) : d120660 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, d120660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, d120660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94355 q = 1) (hb : d116753 q = 1) : d120733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d120733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19950 q ha hb
    | true =>
      simp only [d94355, d120733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19958 q ha hb
  have h7 (q : Pattern) (ha : d8844 q = 1) (hb : d116753 q = 1) : d120751 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, d120751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19940 q ha hb
    | true =>
      simp only [d8844, d120751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19922 q ha hb
  have h8 (q : Pattern) (ha : d94356 q = 1) (hb : d116753 q = 1) : d120752 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d120752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94356, d120752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94357 q = 1) (hb : d116753 q = 1) : d120753 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d120753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94357, d120753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94358 q = 1) (hb : d116753 q = 1) : d120754 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d120754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94358, d120754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94362 q = 1) (hb : d116753 q = 1) : d120758 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d120758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94362, d120758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19959 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d116753 q = 1) : d120760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d120760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d120760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19923 q ha hb
  have h13 (q : Pattern) (ha : d94363 q = 1) (hb : d116753 q = 1) : d120761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d120761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94363, d120761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94364 q = 1) (hb : d116753 q = 1) : d120762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d120762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94364, d120762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94365 q = 1) (hb : d116753 q = 1) : d120763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d120763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94365, d120763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94366 q = 1) (hb : d116753 q = 1) : d120764 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d120764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94366, d120764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94372 q = 1) (hb : d116753 q = 1) : d120817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d120817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94372, d120817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19970 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d116753 q = 1) : d120828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d120828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d120828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19928 q ha hb
  have h19 (q : Pattern) (ha : d94373 q = 1) (hb : d116753 q = 1) : d120829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d120829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94373, d120829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94374 q = 1) (hb : d116753 q = 1) : d120830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d120830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94374, d120830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94375 q = 1) (hb : d116753 q = 1) : d120831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d120831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94375, d120831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94376 q = 1) (hb : d116753 q = 1) : d120832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d120832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94376, d120832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94377 q = 1) (hb : d116753 q = 1) : d120833 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d120833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94377, d120833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19972 (p : Pattern) (ha : d94383 p = 1) (hb : d116753 p = 1) : d120839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d116753 q = 1) : d120834 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d120834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, d120834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19971 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d116753 q = 1) : d120835 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d120835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, d120835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d116753 q = 1) : d120836 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d120836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, d120836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d116753 q = 1) : d120837 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d120837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, d120837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d116753 q = 1) : d120838 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d120838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, d120838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d116753 q = 1) : d120839 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d120839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, d120839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19973 (p : Pattern) (ha : d1581 p = 1) (hb : d116750 p = 1) : d22232 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1568 q = 1) : d1568 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1581 q = 1) (hb : d116750 q = 1) : d22232 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1581, d116750, d22232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1581, d116750, d22232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19974 (p : Pattern) (ha : d1589 p = 1) (hb : d116752 p = 1) : d120844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1588 q = 1) (hb : d116750 q = 1) : d22254 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1588, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1589 q = 1) (hb : d116752 q = 1) : d120844 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1589, d116752, d120844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1589, d116752, d120844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro19975 (p : Pattern) (ha : d1602 p = 1) (hb : d116752 p = 1) : d120849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1588 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1601 q = 1) (hb : d116750 q = 1) : d1601 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1602 q = 1) (hb : d116752 q = 1) : d120849 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1602, d116752, d120849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1602, d116752, d120849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19976 (p : Pattern) (ha : d1613 p = 1) (hb : d116753 p = 1) : d120859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1603 q = 1) (hb : d116752 q = 1) : d120850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19974 q ha hb
    | true =>
      simp only [d1603, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19975 q ha hb
  have h2 (q : Pattern) (ha : d1604 q = 1) (hb : d116752 q = 1) : d120851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1605 q = 1) (hb : d116752 q = 1) : d120852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1607 q = 1) (hb : d116753 q = 1) : d120853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d116753, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1607, d116753, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1612 q = 1) (hb : d116753 q = 1) : d120858 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d120858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1612, d120858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1613 q = 1) (hb : d116753 q = 1) : d120859 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d120859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1613, d120859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19977 (p : Pattern) (ha : d1623 p = 1) (hb : d116753 p = 1) : d120869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d116753 q = 1) : d120866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d116753 q = 1) : d120867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d116753 q = 1) : d120868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d116753 q = 1) : d120869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d120869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d120869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19978 (p : Pattern) (ha : d1633 p = 1) (hb : d116753 p = 1) : d120879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d116753 q = 1) : d120866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d116753 q = 1) : d120867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d116753 q = 1) : d120868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d116753 q = 1) : d120879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d120879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d120879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19979 (p : Pattern) (ha : d1838 p = 1) (hb : d116753 p = 1) : d120978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d116753 q = 1) : d120967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19977 q ha hb
    | true =>
      simp only [d1827, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d116753 q = 1) : d120968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d116753 q = 1) : d120969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d116753 q = 1) : d120970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d116753 q = 1) : d120971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d116753 q = 1) : d120973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19978 q ha hb
    | true =>
      simp only [d1833, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d116753 q = 1) : d120974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d116753 q = 1) : d120975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d116753 q = 1) : d120976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d116753 q = 1) : d120977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d116753 q = 1) : d120978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d120978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d120978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19980 (p : Pattern) (ha : d1847 p = 1) (hb : d116753 p = 1) : d120987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d116753 q = 1) : d120973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19978 q ha hb
    | true =>
      simp only [d1833, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d116753 q = 1) : d120974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d116753 q = 1) : d120975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d116753 q = 1) : d120976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d116753 q = 1) : d120977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d116753 q = 1) : d120987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d120987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d120987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19981 (p : Pattern) (ha : d1878 p = 1) (hb : d116752 p = 1) : d120999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1869 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1870 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1871 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1877 q = 1) (hb : d116750 q = 1) : d22561 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1877, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1878 q = 1) (hb : d116752 q = 1) : d120999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d116752, d120999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1878, d116752, d120999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19982 (p : Pattern) (ha : d1888 p = 1) (hb : d116752 p = 1) : d121016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1877 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1887 q = 1) (hb : d116750 q = 1) : d1887 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1888 q = 1) (hb : d116752 q = 1) : d121016 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1888, d116752, d121016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1888, d116752, d121016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19983 (p : Pattern) (ha : d1907 p = 1) (hb : d116753 p = 1) : d121022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1889 q = 1) (hb : d116752 q = 1) : d121017 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19981 q ha hb
    | true =>
      simp only [d1889, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19982 q ha hb
  have h2 (q : Pattern) (ha : d1890 q = 1) (hb : d116752 q = 1) : d121018 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1891 q = 1) (hb : d116752 q = 1) : d121019 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1897 q = 1) (hb : d116753 q = 1) : d121020 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d116753, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1897, d116753, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1906 q = 1) (hb : d116753 q = 1) : d121021 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d121021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1906, d121021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1907 q = 1) (hb : d116753 q = 1) : d121022 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d121022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1907, d121022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro19984 (p : Pattern) (ha : d1974 p = 1) (hb : d116753 p = 1) : d121049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d116753 q = 1) : d121023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19983 q ha hb
    | true =>
      simp only [d1908, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d116753 q = 1) : d121024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d116753 q = 1) : d121046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d121046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d121046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d116753 q = 1) : d121047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d121047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d121047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d116753 q = 1) : d121048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d121048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d121048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d116753 q = 1) : d121049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d121049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d121049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19985 (p : Pattern) (ha : d1980 p = 1) (hb : d116753 p = 1) : d121055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d116753 q = 1) : d121050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d121050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19984 q ha hb
    | true =>
      simp only [d1975, d121050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d116753 q = 1) : d121051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d121051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d121051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d116753 q = 1) : d121052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d121052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d121052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d116753 q = 1) : d121053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d121053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d121053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d116753 q = 1) : d121054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d121054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d121054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d116753 q = 1) : d121055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d121055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d121055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19986 (p : Pattern) (ha : d1569 p = 1) (hb : d116750 p = 1) : d22219 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1553 q = 1) : d1553 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1568 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1569 q = 1) (hb : d116750 q = 1) : d22219 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1569, d116750, d22219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1569, d116750, d22219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro19987 (p : Pattern) (ha : d1587 p = 1) (hb : d116752 p = 1) : d120843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1586 q = 1) (hb : d116750 q = 1) : d22237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1587 q = 1) (hb : d116752 q = 1) : d120843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1587, d116752, d120843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1587, d116752, d120843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19988 (p : Pattern) (ha : d8911 p = 1) (hb : d116753 p = 1) : d120855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d116752 q = 1) : d120845 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19987 q ha hb
    | true =>
      simp only [d1590, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19974 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d116752 q = 1) : d120846 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d116752 q = 1) : d120847 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d116753 q = 1) : d120848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d116753, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d116753, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1603 q = 1) (hb : d116752 q = 1) : d120850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19974 q ha hb
    | true =>
      simp only [d1603, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19975 q ha hb
  have h7 (q : Pattern) (ha : d1604 q = 1) (hb : d116752 q = 1) : d120851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1605 q = 1) (hb : d116752 q = 1) : d120852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1607 q = 1) (hb : d116753 q = 1) : d120853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d116753, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1607, d116753, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8910 q = 1) (hb : d116753 q = 1) : d120854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, d120854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8910, d120854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8911 q = 1) (hb : d116753 q = 1) : d120855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, d120855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8911, d120855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19989 (p : Pattern) (ha : d8917 p = 1) (hb : d116753 p = 1) : d120865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d116753 q = 1) : d120862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d116753 q = 1) : d120863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d116753 q = 1) : d120864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8917 q = 1) (hb : d116753 q = 1) : d120865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, d120865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, d120865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19990 (p : Pattern) (ha : d8923 p = 1) (hb : d116753 p = 1) : d120875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d116753 q = 1) : d120870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19989 q ha hb
    | true =>
      simp only [d8918, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19977 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d116753 q = 1) : d120871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d116753 q = 1) : d120872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d116753 q = 1) : d120873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d116753 q = 1) : d120874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8923 q = 1) (hb : d116753 q = 1) : d120875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d120875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d120875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19991 (p : Pattern) (ha : d8926 p = 1) (hb : d116753 p = 1) : d120878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d116753 q = 1) : d120862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d116753 q = 1) : d120863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d116753 q = 1) : d120864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8926 q = 1) (hb : d116753 q = 1) : d120878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, d120878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8926, d120878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19992 (p : Pattern) (ha : d8932 p = 1) (hb : d116753 p = 1) : d120885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d116753 q = 1) : d120870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19989 q ha hb
    | true =>
      simp only [d8918, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19977 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d116753 q = 1) : d120871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d116753 q = 1) : d120872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d116753 q = 1) : d120873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d116753 q = 1) : d120874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8927 q = 1) (hb : d116753 q = 1) : d120880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19991 q ha hb
    | true =>
      simp only [d8927, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19978 q ha hb
  have h7 (q : Pattern) (ha : d8928 q = 1) (hb : d116753 q = 1) : d120881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8929 q = 1) (hb : d116753 q = 1) : d120882 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8929, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8930 q = 1) (hb : d116753 q = 1) : d120883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8931 q = 1) (hb : d116753 q = 1) : d120884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8932 q = 1) (hb : d116753 q = 1) : d120885 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d120885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8932, d120885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19993 (p : Pattern) (ha : d5120 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5120 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5120, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19994 (p : Pattern) (ha : d5139 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5139 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5139, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5139, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro19995 (p : Pattern) (ha : d7036 p = 1) (hb : d116753 p = 1) : d120916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d116752 q = 1) : d120845 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19987 q ha hb
    | true =>
      simp only [d1590, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19974 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d116752 q = 1) : d120846 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d116752 q = 1) : d120847 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d116753 q = 1) : d120848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d116753, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d116753, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5140 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19993 q ha hb
    | true =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19994 q ha hb
  have h7 (q : Pattern) (ha : d5141 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5142 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5143 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5143, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d7035 q = 1) (hb : d116753 q = 1) : d120915 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, d120915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7035, d120915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7036 q = 1) (hb : d116753 q = 1) : d120916 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, d120916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7036, d120916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19996 (p : Pattern) (ha : d8960 p = 1) (hb : d116753 p = 1) : d120926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d116753 q = 1) : d120917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19995 q ha hb
    | true =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d116753 q = 1) : d120918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d116753 q = 1) : d120923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d116753 q = 1) : d120924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d116753 q = 1) : d120925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8960 q = 1) (hb : d116753 q = 1) : d120926 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, d120926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, d120926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19997 (p : Pattern) (ha : d9011 p = 1) (hb : d116753 p = 1) : d120972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9006 q = 1) (hb : d116753 q = 1) : d120962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, d120962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19996 q ha hb
    | true =>
      simp only [d9006, d120962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19977 q ha hb
  have h2 (q : Pattern) (ha : d9007 q = 1) (hb : d116753 q = 1) : d120963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, d120963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, d120963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9008 q = 1) (hb : d116753 q = 1) : d120964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, d120964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9008, d120964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9009 q = 1) (hb : d116753 q = 1) : d120965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, d120965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, d120965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9010 q = 1) (hb : d116753 q = 1) : d120966 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, d120966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, d120966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d116753 q = 1) : d120967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19977 q ha hb
    | true =>
      simp only [d1827, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d116753 q = 1) : d120968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d116753 q = 1) : d120969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d116753 q = 1) : d120970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d116753 q = 1) : d120971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9011 q = 1) (hb : d116753 q = 1) : d120972 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, d120972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9011, d120972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19998 (p : Pattern) (ha : d1646 p = 1) (hb : d116753 p = 1) : d120892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d116753 q = 1) : d120866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d116753 q = 1) : d120867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d116753 q = 1) : d120891 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d116753 q = 1) : d120892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d120892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d120892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19999 (p : Pattern) (ha : d1656 p = 1) (hb : d116753 p = 1) : d120902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d116753 q = 1) : d120866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d116753 q = 1) : d120900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d116753 q = 1) : d120901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d116753 q = 1) : d120902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d120902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d120902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
