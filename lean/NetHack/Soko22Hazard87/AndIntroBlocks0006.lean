import NetHack.Soko22Hazard87.AndIntroBlocks0005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro1500 (p : Pattern) (ha : d51754 p = 1) (hb : d61359 p = 1) : d61594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1169 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1170 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1168 q = 1) : d1168 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1178 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1179 q = 1) (hb : d61357 q = 1) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1180 q = 1) (hb : d61357 q = 1) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1181 q = 1) (hb : d61357 q = 1) : d3396 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1181, d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51738 q = 1) : d51738 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51742 q = 1) (hb : d61357 q = 1) : d61589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d61357, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51742, d61357, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d1355 q = 1) : d1355 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1361 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1362 q = 1) (hb : d61357 q = 1) : d3398 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d61357, d3398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d1362, d61357, d3398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51743 q = 1) (hb : d61357 q = 1) : d61590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51743, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51744 q = 1) (hb : d61357 q = 1) : d61591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51744, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51745 q = 1) (hb : d61357 q = 1) : d61592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51745, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4499 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4500 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d1370 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1371 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51746 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51747 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51748 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51749 q = 1) (hb : d61357 q = 1) : d61593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51749, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d4509 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4510 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d51750 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51750, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d51750, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d51751 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51752 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h34 (q : Pattern) (ha : d51753 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d51753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h35 (q : Pattern) (ha : d51754 q = 1) (hb : d61359 q = 1) : d61594 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51754, d61359, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51754, d61359, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro1501 (p : Pattern) (ha : d51760 p = 1) (hb : d61359 p = 1) : d61600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51755 q = 1) (hb : d61359 q = 1) : d61595 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51755, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51755, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1500 q ha hb
  have h2 (q : Pattern) (ha : d51756 q = 1) (hb : d61359 q = 1) : d61596 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51756, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51756, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51757 q = 1) (hb : d61359 q = 1) : d61597 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51757, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51757, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51758 q = 1) (hb : d61359 q = 1) : d61598 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51758, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51758, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51759 q = 1) (hb : d61359 q = 1) : d61599 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51759, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51759, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51760 q = 1) (hb : d61359 q = 1) : d61600 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51760, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51760, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1502 (p : Pattern) (ha : d51782 p = 1) (hb : d61359 p = 1) : d61609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1630 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1631 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1639 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1640 q = 1) (hb : d61357 q = 1) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1641 q = 1) (hb : d61357 q = 1) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1642 q = 1) (hb : d61357 q = 1) : d3415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1642, d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51766 q = 1) : d51766 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51770 q = 1) (hb : d61357 q = 1) : d61604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d61357, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51770, d61357, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d1832 q = 1) : d1832 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1838 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1839 q = 1) (hb : d61357 q = 1) : d3417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d61357, d3417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d1839, d61357, d3417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51771 q = 1) (hb : d61357 q = 1) : d61605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51771, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51772 q = 1) (hb : d61357 q = 1) : d61606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51772, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51773 q = 1) (hb : d61357 q = 1) : d61607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51773, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4539 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4540 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d1847 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1848 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51774 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51775 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51776 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51777 q = 1) (hb : d61357 q = 1) : d61608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51777, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d4549 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4550 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d51778 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51778, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d51778, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d51779 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51780 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h34 (q : Pattern) (ha : d51781 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d51781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h35 (q : Pattern) (ha : d51782 q = 1) (hb : d61359 q = 1) : d61609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51782, d61359, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51782, d61359, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro1503 (p : Pattern) (ha : d51788 p = 1) (hb : d61359 p = 1) : d61615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51783 q = 1) (hb : d61359 q = 1) : d61610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51783, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51783, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1502 q ha hb
  have h2 (q : Pattern) (ha : d51784 q = 1) (hb : d61359 q = 1) : d61611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51784, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51784, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51785 q = 1) (hb : d61359 q = 1) : d61612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51785, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51785, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51786 q = 1) (hb : d61359 q = 1) : d61613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51786, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51786, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51787 q = 1) (hb : d61359 q = 1) : d61614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51787, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51787, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51788 q = 1) (hb : d61359 q = 1) : d61615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51788, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51788, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1504 (p : Pattern) (ha : d51811 p = 1) (hb : d61359 p = 1) : d61625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2113 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2114 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2122 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2123 q = 1) (hb : d61357 q = 1) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2124 q = 1) (hb : d61357 q = 1) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2125 q = 1) (hb : d61357 q = 1) : d3435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2125, d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51795 q = 1) : d51795 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51799 q = 1) (hb : d61357 q = 1) : d61620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d61357, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51799, d61357, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d2310 q = 1) : d2310 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2316 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d2317 q = 1) (hb : d61357 q = 1) : d3437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d61357, d3437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d2317, d61357, d3437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51800 q = 1) (hb : d61357 q = 1) : d61621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51800, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51801 q = 1) (hb : d61357 q = 1) : d61622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51801, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51802 q = 1) (hb : d61357 q = 1) : d61623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51802, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4580 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4581 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d2325 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d2326 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51803 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51804 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51805 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51806 q = 1) (hb : d61357 q = 1) : d61624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51806, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d4590 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4591 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d51807 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51807, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d51807, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d51808 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51809 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h34 (q : Pattern) (ha : d51810 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d51810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h35 (q : Pattern) (ha : d51811 q = 1) (hb : d61359 q = 1) : d61625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51811, d61359, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51811, d61359, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro1505 (p : Pattern) (ha : d51817 p = 1) (hb : d61359 p = 1) : d61631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51812 q = 1) (hb : d61359 q = 1) : d61626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51812, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51812, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1504 q ha hb
  have h2 (q : Pattern) (ha : d51813 q = 1) (hb : d61359 q = 1) : d61627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51813, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51813, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51814 q = 1) (hb : d61359 q = 1) : d61628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51814, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51814, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51815 q = 1) (hb : d61359 q = 1) : d61629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51815, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51815, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51816 q = 1) (hb : d61359 q = 1) : d61630 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51816, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51816, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51817 q = 1) (hb : d61359 q = 1) : d61631 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51817, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51817, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1506 (p : Pattern) (ha : d51823 p = 1) (hb : d61359 p = 1) : d61637 p = 1 := by
  have h0 (q : Pattern) (ha : d51708 q = 1) (hb : d61359 q = 1) : d61574 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51708, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1495 q ha hb
    | true =>
      simp only [d51708, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1497 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51734 q = 1) (hb : d61359 q = 1) : d61587 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51734, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51734, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1499 q ha hb
  have h3 (q : Pattern) (ha : d51735 q = 1) (hb : d61359 q = 1) : d61588 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51735, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51735, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51761 q = 1) (hb : d61359 q = 1) : d61601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51761, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51761, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1501 q ha hb
  have h5 (q : Pattern) (ha : d51762 q = 1) (hb : d61359 q = 1) : d61602 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51762, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51762, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51763 q = 1) (hb : d61359 q = 1) : d61603 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51763, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51763, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51789 q = 1) (hb : d61359 q = 1) : d61616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51789, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51789, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1503 q ha hb
  have h8 (q : Pattern) (ha : d51790 q = 1) (hb : d61359 q = 1) : d61617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51790, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51790, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51791 q = 1) (hb : d61359 q = 1) : d61618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51791, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51791, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51792 q = 1) (hb : d61359 q = 1) : d61619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51792, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51792, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51818 q = 1) (hb : d61359 q = 1) : d61632 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51818, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51818, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1505 q ha hb
  have h12 (q : Pattern) (ha : d51819 q = 1) (hb : d61359 q = 1) : d61633 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51819, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51819, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51820 q = 1) (hb : d61359 q = 1) : d61634 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51820, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51820, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51821 q = 1) (hb : d61359 q = 1) : d61635 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51821, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51821, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51822 q = 1) (hb : d61359 q = 1) : d61636 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d51822, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51822, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51823 q = 1) (hb : d61359 q = 1) : d61637 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d51823, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51823, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1507 (p : Pattern) (ha : d51829 p = 1) (hb : d61359 p = 1) : d61643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51824 q = 1) (hb : d61359 q = 1) : d61638 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d51824, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1506 q ha hb
    | true =>
      simp only [d51824, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51825 q = 1) (hb : d61359 q = 1) : d61639 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d51825, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51825, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51826 q = 1) (hb : d61359 q = 1) : d61640 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d51826, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51826, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51827 q = 1) (hb : d61359 q = 1) : d61641 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d51827, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51827, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51828 q = 1) (hb : d61359 q = 1) : d61642 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d51828, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51828, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51829 q = 1) (hb : d61359 q = 1) : d61643 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d51829, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51829, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1508 (p : Pattern) (ha : d51835 p = 1) (hb : d61359 p = 1) : d61649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51830 q = 1) (hb : d61359 q = 1) : d61644 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d51830, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1507 q ha hb
    | true =>
      simp only [d51830, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51831 q = 1) (hb : d61359 q = 1) : d61645 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d51831, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51831, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51832 q = 1) (hb : d61359 q = 1) : d61646 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d51832, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51832, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51833 q = 1) (hb : d61359 q = 1) : d61647 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d51833, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51833, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51834 q = 1) (hb : d61359 q = 1) : d61648 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d51834, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51834, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51835 q = 1) (hb : d61359 q = 1) : d61649 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d51835, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51835, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1509 (p : Pattern) (ha : d51841 p = 1) (hb : d61359 p = 1) : d61655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51836 q = 1) (hb : d61359 q = 1) : d61650 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d51836, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1508 q ha hb
    | true =>
      simp only [d51836, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51837 q = 1) (hb : d61359 q = 1) : d61651 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d51837, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51837, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51838 q = 1) (hb : d61359 q = 1) : d61652 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d51838, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51838, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51839 q = 1) (hb : d61359 q = 1) : d61653 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d51839, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51839, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51840 q = 1) (hb : d61359 q = 1) : d61654 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d51840, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51840, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51841 q = 1) (hb : d61359 q = 1) : d61655 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d51841, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51841, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1510 (p : Pattern) (ha : d51847 p = 1) (hb : d61359 p = 1) : d61661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51842 q = 1) (hb : d61359 q = 1) : d61656 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d51842, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1509 q ha hb
    | true =>
      simp only [d51842, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51843 q = 1) (hb : d61359 q = 1) : d61657 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d51843, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51843, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51844 q = 1) (hb : d61359 q = 1) : d61658 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d51844, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51844, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51845 q = 1) (hb : d61359 q = 1) : d61659 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d51845, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51845, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51846 q = 1) (hb : d61359 q = 1) : d61660 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d51846, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51846, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51847 q = 1) (hb : d61359 q = 1) : d61661 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d51847, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51847, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1511 (p : Pattern) (ha : d51853 p = 1) (hb : d61359 p = 1) : d61667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51848 q = 1) (hb : d61359 q = 1) : d61662 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d51848, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1510 q ha hb
    | true =>
      simp only [d51848, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51849 q = 1) (hb : d61359 q = 1) : d61663 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d51849, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51849, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51850 q = 1) (hb : d61359 q = 1) : d61664 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d51850, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51850, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51851 q = 1) (hb : d61359 q = 1) : d61665 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d51851, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51851, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51852 q = 1) (hb : d61359 q = 1) : d61666 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d51852, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51852, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51853 q = 1) (hb : d61359 q = 1) : d61667 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d51853, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51853, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1512 (p : Pattern) (ha : d51859 p = 1) (hb : d61360 p = 1) : d61673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51854 q = 1) (hb : d61359 q = 1) : d61668 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d51854, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1511 q ha hb
    | true =>
      simp only [d51854, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51855 q = 1) (hb : d61359 q = 1) : d61669 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d51855, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51855, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51856 q = 1) (hb : d61359 q = 1) : d61670 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d51856, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51856, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51857 q = 1) (hb : d61359 q = 1) : d61671 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d51857, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51857, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51858 q = 1) (hb : d61360 q = 1) : d61672 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d51858, d61360, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51858, d61360, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d61360 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51859 q = 1) (hb : d61360 q = 1) : d61673 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d51859, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51859, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1513 (p : Pattern) (ha : d51865 p = 1) (hb : d61360 p = 1) : d61679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51860 q = 1) (hb : d61360 q = 1) : d61674 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d51860, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1512 q ha hb
    | true =>
      simp only [d51860, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51861 q = 1) (hb : d61360 q = 1) : d61675 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d51861, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51861, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51862 q = 1) (hb : d61360 q = 1) : d61676 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d51862, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51862, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51863 q = 1) (hb : d61360 q = 1) : d61677 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d51863, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51863, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51864 q = 1) (hb : d61360 q = 1) : d61678 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d51864, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51864, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51865 q = 1) (hb : d61360 q = 1) : d61679 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d51865, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51865, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1514 (p : Pattern) (ha : d3324 p = 1) (hb : d61366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3319 q = 1) (hb : d61361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d61361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6 q ha hb
    | true =>
      simp only [d3319, d61361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3320 q = 1) (hb : d61362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, d61362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3320, d61362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3321 q = 1) (hb : d61363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, d61363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3321, d61363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3322 q = 1) (hb : d61364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, d61364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3322, d61364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3323 q = 1) (hb : d61365 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, d61365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3323, d61365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3324 q = 1) (hb : d61366 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, d61366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3324, d61366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1515 (p : Pattern) (ha : d61379 p = 1) (hb : d61544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3329 q = 1) (hb : d61371 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d61371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d61371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3330 q = 1) (hb : d61372 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d61372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3330, d61372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3331 q = 1) (hb : d61373 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d61373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d61373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61374 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61374, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q hb ha
    | true =>
      simp only [d61374, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61375 q = 1) (hb : d61540 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61375, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61375, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61376 q = 1) (hb : d61541 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61376, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61376, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61377 q = 1) (hb : d61542 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61377, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61377, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61378 q = 1) (hb : d61543 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61378, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61378, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61379 q = 1) (hb : d61544 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61379, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61379, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1516 (p : Pattern) (ha : d61394 p = 1) (hb : d61555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3343 q = 1) (hb : d61385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d61385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d3343, d61385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3344 q = 1) (hb : d61386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d61386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3344, d61386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3345 q = 1) (hb : d61387 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d61387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d61387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61388 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61388, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q hb ha
    | true =>
      simp only [d61388, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d3347 q = 1) (hb : d61389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d61389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d3347, d61389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61390 q = 1) (hb : d61551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61390, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61390, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61391 q = 1) (hb : d61552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61391, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61391, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61392 q = 1) (hb : d61553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61392, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61392, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61393 q = 1) (hb : d61554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61393, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61393, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61394 q = 1) (hb : d61555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61394, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61394, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1517 (p : Pattern) (ha : d61400 p = 1) (hb : d61561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d61367 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d61367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d61367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1514 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d61368 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d61368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d61368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d61369 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d61369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d61369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d61370 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d61370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d61370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61380 q = 1) (hb : d61545 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61380, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61380, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1515 q ha hb
  have h6 (q : Pattern) (ha : d61381 q = 1) (hb : d61546 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61381, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61381, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61382 q = 1) (hb : d61547 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61382, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61382, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61383 q = 1) (hb : d61548 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61383, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61383, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61384 q = 1) (hb : d61549 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61384, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61384, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61395 q = 1) (hb : d61556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61395, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61395, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1516 q ha hb
  have h11 (q : Pattern) (ha : d61396 q = 1) (hb : d61557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61396, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61396, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61397 q = 1) (hb : d61558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61397, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61397, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61398 q = 1) (hb : d61559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61398, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61398, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61399 q = 1) (hb : d61560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61399, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61399, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61400 q = 1) (hb : d61561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61400, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61400, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1518 (p : Pattern) (ha : d61410 p = 1) (hb : d61567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3359 q = 1) (hb : d61401 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d61401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d3359, d61401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3360 q = 1) (hb : d61402 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d61402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3360, d61402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3361 q = 1) (hb : d61403 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d61403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d61403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61404 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61404, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q hb ha
    | true =>
      simp only [d61404, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d3363 q = 1) (hb : d61405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d61405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d3363, d61405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61406 q = 1) (hb : d61563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61406, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61406, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61407 q = 1) (hb : d61564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61407, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61407, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61408 q = 1) (hb : d61565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61408, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61408, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61409 q = 1) (hb : d61566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61409, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61409, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61410 q = 1) (hb : d61567 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61410, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61410, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1519 (p : Pattern) (ha : d61416 p = 1) (hb : d61573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61411 q = 1) (hb : d61568 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61411, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61411, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1518 q ha hb
  have h2 (q : Pattern) (ha : d61412 q = 1) (hb : d61569 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61412, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61412, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61413 q = 1) (hb : d61570 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61413, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61413, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61414 q = 1) (hb : d61571 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61414, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61414, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61415 q = 1) (hb : d61572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61415, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61415, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61416 q = 1) (hb : d61573 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61416, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61416, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1520 (p : Pattern) (ha : d61427 p = 1) (hb : d61580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3376 q = 1) (hb : d61418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d61418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d3376, d61418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3377 q = 1) (hb : d61419 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d61419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3377, d61419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3378 q = 1) (hb : d61420 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d61420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d61420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61421 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61421, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q hb ha
    | true =>
      simp only [d61421, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d3380 q = 1) (hb : d61422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d61422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d3380, d61422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61423 q = 1) (hb : d61576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61423, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61423, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61424 q = 1) (hb : d61577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61424, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61424, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61425 q = 1) (hb : d61578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61425, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61425, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61426 q = 1) (hb : d61579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61426, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61426, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61427 q = 1) (hb : d61580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61427, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61427, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1521 (p : Pattern) (ha : d61433 p = 1) (hb : d61586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61428 q = 1) (hb : d61581 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61428, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61428, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1520 q ha hb
  have h2 (q : Pattern) (ha : d61429 q = 1) (hb : d61582 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61429, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61429, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61430 q = 1) (hb : d61583 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61430, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61430, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61431 q = 1) (hb : d61584 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61431, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61431, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61432 q = 1) (hb : d61585 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61432, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61432, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61433 q = 1) (hb : d61586 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61433, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61433, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1522 (p : Pattern) (ha : d61445 p = 1) (hb : d61594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3394 q = 1) (hb : d61436 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d61436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d3394, d61436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3395 q = 1) (hb : d61437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d61437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3395, d61437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3396 q = 1) (hb : d61438 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d61438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d61438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61439 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61439, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q hb ha
    | true =>
      simp only [d61439, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d3398 q = 1) (hb : d61440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d61440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d3398, d61440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61441 q = 1) (hb : d61590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61441, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61441, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61442 q = 1) (hb : d61591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61442, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61442, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61443 q = 1) (hb : d61592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61443, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61443, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61444 q = 1) (hb : d61593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61444, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61444, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61445 q = 1) (hb : d61594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61445, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61445, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1523 (p : Pattern) (ha : d61451 p = 1) (hb : d61600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61446 q = 1) (hb : d61595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61446, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61446, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1522 q ha hb
  have h2 (q : Pattern) (ha : d61447 q = 1) (hb : d61596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61447, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61447, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61448 q = 1) (hb : d61597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61448, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61448, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61449 q = 1) (hb : d61598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61449, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61449, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61450 q = 1) (hb : d61599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61450, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61450, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61451 q = 1) (hb : d61600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61451, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61451, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1524 (p : Pattern) (ha : d61464 p = 1) (hb : d61609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3413 q = 1) (hb : d61455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d61455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d3413, d61455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3414 q = 1) (hb : d61456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d61456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3414, d61456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3415 q = 1) (hb : d61457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d61457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d61457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61458 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61458, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q hb ha
    | true =>
      simp only [d61458, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d3417 q = 1) (hb : d61459 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d61459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d3417, d61459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61460 q = 1) (hb : d61605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61460, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61460, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61461 q = 1) (hb : d61606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61461, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61461, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61462 q = 1) (hb : d61607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61462, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61462, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61463 q = 1) (hb : d61608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61463, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61463, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61464 q = 1) (hb : d61609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61464, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61464, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1525 (p : Pattern) (ha : d61470 p = 1) (hb : d61615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61465 q = 1) (hb : d61610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61465, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61465, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1524 q ha hb
  have h2 (q : Pattern) (ha : d61466 q = 1) (hb : d61611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61466, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61466, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61467 q = 1) (hb : d61612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61467, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61467, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61468 q = 1) (hb : d61613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61468, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61468, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61469 q = 1) (hb : d61614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61469, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61469, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61470 q = 1) (hb : d61615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61470, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61470, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1526 (p : Pattern) (ha : d61484 p = 1) (hb : d61625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3433 q = 1) (hb : d61475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d61475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d3433, d61475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3434 q = 1) (hb : d61476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d61476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3434, d61476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3435 q = 1) (hb : d61477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d61477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d61477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61478 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61478, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q hb ha
    | true =>
      simp only [d61478, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d3437 q = 1) (hb : d61479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d61479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d3437, d61479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61480 q = 1) (hb : d61621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61480, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61480, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61481 q = 1) (hb : d61622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61481, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61481, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61482 q = 1) (hb : d61623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61482, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61482, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61483 q = 1) (hb : d61624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61483, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61483, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61484 q = 1) (hb : d61625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61484, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61484, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro1527 (p : Pattern) (ha : d61490 p = 1) (hb : d61631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61485 q = 1) (hb : d61626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61485, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61485, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1526 q ha hb
  have h2 (q : Pattern) (ha : d61486 q = 1) (hb : d61627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61486, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61486, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61487 q = 1) (hb : d61628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61487, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61487, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61488 q = 1) (hb : d61629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61488, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61488, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61489 q = 1) (hb : d61630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61489, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61489, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61490 q = 1) (hb : d61631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61490, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61490, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1528 (p : Pattern) (ha : d61496 p = 1) (hb : d61637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61417 q = 1) (hb : d61574 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61417, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1517 q ha hb
    | true =>
      simp only [d61417, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1519 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61434 q = 1) (hb : d61587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61434, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61434, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1521 q ha hb
  have h3 (q : Pattern) (ha : d61435 q = 1) (hb : d61588 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61435, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61435, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61452 q = 1) (hb : d61601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61452, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61452, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1523 q ha hb
  have h5 (q : Pattern) (ha : d61453 q = 1) (hb : d61602 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61453, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61453, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61454 q = 1) (hb : d61603 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61454, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61454, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61471 q = 1) (hb : d61616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61471, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61471, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1525 q ha hb
  have h8 (q : Pattern) (ha : d61472 q = 1) (hb : d61617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61472, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61472, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61473 q = 1) (hb : d61618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61473, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61473, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61474 q = 1) (hb : d61619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61474, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61474, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61491 q = 1) (hb : d61632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61491, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61491, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1527 q ha hb
  have h12 (q : Pattern) (ha : d61492 q = 1) (hb : d61633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61492, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61492, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61493 q = 1) (hb : d61634 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61493, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61493, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61494 q = 1) (hb : d61635 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61494, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61494, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61495 q = 1) (hb : d61636 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61495, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61495, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61496 q = 1) (hb : d61637 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61496, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61496, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro1529 (p : Pattern) (ha : d61502 p = 1) (hb : d61643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61497 q = 1) (hb : d61638 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61497, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1528 q ha hb
    | true =>
      simp only [d61497, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61498 q = 1) (hb : d61639 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61498, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61498, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61499 q = 1) (hb : d61640 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61499, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61499, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61500 q = 1) (hb : d61641 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61500, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61500, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61501 q = 1) (hb : d61642 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61501, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61501, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61502 q = 1) (hb : d61643 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61502, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61502, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1530 (p : Pattern) (ha : d61508 p = 1) (hb : d61649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61503 q = 1) (hb : d61644 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61503, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1529 q ha hb
    | true =>
      simp only [d61503, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61504 q = 1) (hb : d61645 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61504, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61504, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61505 q = 1) (hb : d61646 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61505, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61505, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61506 q = 1) (hb : d61647 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61506, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61506, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61507 q = 1) (hb : d61648 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61507, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61507, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61508 q = 1) (hb : d61649 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61508, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61508, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1531 (p : Pattern) (ha : d61514 p = 1) (hb : d61655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61509 q = 1) (hb : d61650 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61509, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1530 q ha hb
    | true =>
      simp only [d61509, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61510 q = 1) (hb : d61651 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61510, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61510, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61511 q = 1) (hb : d61652 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61511, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61511, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61512 q = 1) (hb : d61653 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61512, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61512, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61513 q = 1) (hb : d61654 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61513, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61513, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61514 q = 1) (hb : d61655 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61514, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61514, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1532 (p : Pattern) (ha : d61520 p = 1) (hb : d61661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61515 q = 1) (hb : d61656 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61515, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1531 q ha hb
    | true =>
      simp only [d61515, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61516 q = 1) (hb : d61657 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61516, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61516, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61517 q = 1) (hb : d61658 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61517, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61517, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61518 q = 1) (hb : d61659 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61518, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61518, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61519 q = 1) (hb : d61660 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61519, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61519, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61520 q = 1) (hb : d61661 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61520, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61520, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1533 (p : Pattern) (ha : d61526 p = 1) (hb : d61667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61521 q = 1) (hb : d61662 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61521, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1532 q ha hb
    | true =>
      simp only [d61521, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61522 q = 1) (hb : d61663 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61522, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61522, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61523 q = 1) (hb : d61664 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61523, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61523, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61524 q = 1) (hb : d61665 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61524, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61524, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61525 q = 1) (hb : d61666 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61525, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61525, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61526 q = 1) (hb : d61667 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61526, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61526, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1534 (p : Pattern) (ha : d61532 p = 1) (hb : d61673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61527 q = 1) (hb : d61668 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61527, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1533 q ha hb
    | true =>
      simp only [d61527, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61528 q = 1) (hb : d61669 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61528, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61528, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61529 q = 1) (hb : d61670 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61529, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61529, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61530 q = 1) (hb : d61671 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61530, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61530, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61531 q = 1) (hb : d61672 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61531, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61531, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61532 q = 1) (hb : d61673 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61532, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61532, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1535 (p : Pattern) (ha : d61538 p = 1) (hb : d61679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61533 q = 1) (hb : d61674 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61533, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1534 q ha hb
    | true =>
      simp only [d61533, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61534 q = 1) (hb : d61675 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61534, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61534, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61535 q = 1) (hb : d61676 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61535, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61535, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61536 q = 1) (hb : d61677 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61536, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61536, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61537 q = 1) (hb : d61678 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61537, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61537, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61538 q = 1) (hb : d61679 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61538, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61538, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1536 (p : Pattern) (ha : d53647 p = 1) (hb : d61359 p = 1) : d61683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d104 q = 1) : d104 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d61357 q = 1) : d3329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d61357 q = 1) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d61357 q = 1) : d61680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53637, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d61357 q = 1) : d61681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d407 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53639 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53640 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53641 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53642 q = 1) (hb : d61357 q = 1) : d61682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d462 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d463 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d463, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53643 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53643, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53644 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53645 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53646 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53647 q = 1) (hb : d61359 q = 1) : d61683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d61359, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53647, d61359, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1537 (p : Pattern) (ha : d53671 p = 1) (hb : d61359 p = 1) : d61692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d284 q = 1) : d284 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d61357 q = 1) : d3343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d61357 q = 1) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53653 q = 1) (hb : d61357 q = 1) : d61689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53653, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d61357 q = 1) : d61690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53655 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53656 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53656, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53657 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53658 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53659 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53660 q = 1) (hb : d61357 q = 1) : d61691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53660, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53666 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53666, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53667 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53667, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53668 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53669 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53670 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53671 q = 1) (hb : d61359 q = 1) : d61692 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d61359, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53671, d61359, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1538 (p : Pattern) (ha : d53677 p = 1) (hb : d61359 p = 1) : d61698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d61359 q = 1) : d61684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1536 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d61359 q = 1) : d61685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d61359 q = 1) : d61686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d61359 q = 1) : d61687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d61359 q = 1) : d61688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d61359 q = 1) : d61693 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1537 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d61359 q = 1) : d61694 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d61359 q = 1) : d61695 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d61359 q = 1) : d61696 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d61359 q = 1) : d61697 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d61359 q = 1) : d61698 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro1539 (p : Pattern) (ha : d53697 p = 1) (hb : d61359 p = 1) : d61702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d497 q = 1) : d497 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d507 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d61357 q = 1) : d3359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d61357 q = 1) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53678 q = 1) (hb : d61357 q = 1) : d61699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53678, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d61357 q = 1) : d61700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53680 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53681 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53681, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53682 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53683 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53684 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53685 q = 1) (hb : d61357 q = 1) : d61701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53685, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53691 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53692 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53692, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53693 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53693, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53694 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53695 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53696 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53697 q = 1) (hb : d61359 q = 1) : d61702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d61359, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53697, d61359, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1540 (p : Pattern) (ha : d53703 p = 1) (hb : d61359 p = 1) : d61708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d61359 q = 1) : d61703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1539 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d61359 q = 1) : d61704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d61359 q = 1) : d61705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d61359 q = 1) : d61706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d61359 q = 1) : d61707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d61359 q = 1) : d61708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1541 (p : Pattern) (ha : d53724 p = 1) (hb : d61359 p = 1) : d61713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d789 q = 1) : d789 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d799 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d61357 q = 1) : d3376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d61357 q = 1) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53705 q = 1) (hb : d61357 q = 1) : d61710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53705, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d61357 q = 1) : d61711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53707 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53708 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53708, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53709 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53710 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53711 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53712 q = 1) (hb : d61357 q = 1) : d61712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53712, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53718 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53719 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53719, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53720 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53720, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53721 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53722 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53723 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53724 q = 1) (hb : d61359 q = 1) : d61713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d61359, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53724, d61359, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1542 (p : Pattern) (ha : d53730 p = 1) (hb : d61359 p = 1) : d61719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d61359 q = 1) : d61714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1541 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d61359 q = 1) : d61715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d61359 q = 1) : d61716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d61359 q = 1) : d61717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d61359 q = 1) : d61718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d61359 q = 1) : d61719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1543 (p : Pattern) (ha : d53752 p = 1) (hb : d61359 p = 1) : d61725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1168 q = 1) : d1168 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d61357 q = 1) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d61357 q = 1) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53733 q = 1) (hb : d61357 q = 1) : d61722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53733, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d61357 q = 1) : d61723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53735 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53736 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53736, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53737 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53738 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53739 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53740 q = 1) (hb : d61357 q = 1) : d61724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53740, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53746 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53747 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53747, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53748 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53748, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53749 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53750 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53751 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53752 q = 1) (hb : d61359 q = 1) : d61725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d61359, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53752, d61359, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1544 (p : Pattern) (ha : d53758 p = 1) (hb : d61359 p = 1) : d61731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d61359 q = 1) : d61726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1543 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d61359 q = 1) : d61727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d61359 q = 1) : d61728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d61359 q = 1) : d61729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d61359 q = 1) : d61730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d61359 q = 1) : d61731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1545 (p : Pattern) (ha : d53781 p = 1) (hb : d61359 p = 1) : d61738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d61357 q = 1) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d61357 q = 1) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d61357 q = 1) : d61735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53762, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d61357 q = 1) : d61736 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53764 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53765 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53765, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53766 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53767 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53768 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53769 q = 1) (hb : d61357 q = 1) : d61737 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53769, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53775 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53776 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53776, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53777 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53777, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53778 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53779 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53780 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53781 q = 1) (hb : d61359 q = 1) : d61738 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d61359, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53781, d61359, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1546 (p : Pattern) (ha : d53787 p = 1) (hb : d61359 p = 1) : d61744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d61359 q = 1) : d61739 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1545 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d61359 q = 1) : d61740 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d61359 q = 1) : d61741 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d61359 q = 1) : d61742 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d61359 q = 1) : d61743 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d61359 q = 1) : d61744 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1547 (p : Pattern) (ha : d53811 p = 1) (hb : d61359 p = 1) : d61752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d61357 q = 1) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d61357 q = 1) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d61357 q = 1) : d61749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53792, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d61357 q = 1) : d61750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53794 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53795 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53795, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53796 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53797 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53798 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53799 q = 1) (hb : d61357 q = 1) : d61751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53799, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53805 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53806 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53806, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53807 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53807, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d53808 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53809 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d53810 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d53811 q = 1) (hb : d61359 q = 1) : d61752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d61359, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53811, d61359, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1548 (p : Pattern) (ha : d53817 p = 1) (hb : d61359 p = 1) : d61758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d61359 q = 1) : d61753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1547 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d61359 q = 1) : d61754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d61359 q = 1) : d61755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d61359 q = 1) : d61756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d61359 q = 1) : d61757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d61359 q = 1) : d61758 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1549 (p : Pattern) (ha : d53823 p = 1) (hb : d61359 p = 1) : d61764 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d61359 q = 1) : d61709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1538 q ha hb
    | true =>
      simp only [d53704, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1540 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d61359 q = 1) : d61720 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1542 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d61359 q = 1) : d61721 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d61359 q = 1) : d61732 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1544 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d61359 q = 1) : d61733 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d61359 q = 1) : d61734 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d61359 q = 1) : d61745 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1546 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d61359 q = 1) : d61746 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d61359 q = 1) : d61747 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d61359 q = 1) : d61748 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d61359 q = 1) : d61759 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1548 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d61359 q = 1) : d61760 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d61359 q = 1) : d61761 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d61359 q = 1) : d61762 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d61359 q = 1) : d61763 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d61359 q = 1) : d61764 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1550 (p : Pattern) (ha : d53829 p = 1) (hb : d61359 p = 1) : d61770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d61359 q = 1) : d61765 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1549 q ha hb
    | true =>
      simp only [d53824, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d61359 q = 1) : d61766 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d61359 q = 1) : d61767 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d61359 q = 1) : d61768 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d61359 q = 1) : d61769 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d61359 q = 1) : d61770 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1551 (p : Pattern) (ha : d53835 p = 1) (hb : d61359 p = 1) : d61776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d61359 q = 1) : d61771 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1550 q ha hb
    | true =>
      simp only [d53830, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d61359 q = 1) : d61772 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d61359 q = 1) : d61773 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d61359 q = 1) : d61774 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d61359 q = 1) : d61775 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d61359 q = 1) : d61776 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1552 (p : Pattern) (ha : d53841 p = 1) (hb : d61359 p = 1) : d61782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d61359 q = 1) : d61777 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1551 q ha hb
    | true =>
      simp only [d53836, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d61359 q = 1) : d61778 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d61359 q = 1) : d61779 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d61359 q = 1) : d61780 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d61359 q = 1) : d61781 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d61359 q = 1) : d61782 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1553 (p : Pattern) (ha : d53847 p = 1) (hb : d61359 p = 1) : d61788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d61359 q = 1) : d61783 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1552 q ha hb
    | true =>
      simp only [d53842, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d61359 q = 1) : d61784 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d61359 q = 1) : d61785 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d61359 q = 1) : d61786 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d61359 q = 1) : d61787 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d61359 q = 1) : d61788 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1554 (p : Pattern) (ha : d53853 p = 1) (hb : d61359 p = 1) : d61794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d61359 q = 1) : d61789 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1553 q ha hb
    | true =>
      simp only [d53848, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d61359 q = 1) : d61790 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d61359 q = 1) : d61791 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d61359 q = 1) : d61792 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d61359 q = 1) : d61793 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d61359 q = 1) : d61794 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1555 (p : Pattern) (ha : d53859 p = 1) (hb : d61360 p = 1) : d61800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d61359 q = 1) : d61795 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1554 q ha hb
    | true =>
      simp only [d53854, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d61359 q = 1) : d61796 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d61359 q = 1) : d61797 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d61359 q = 1) : d61798 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53858 q = 1) (hb : d61360 q = 1) : d61799 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d61360, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d61360, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d61360 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53859 q = 1) (hb : d61360 q = 1) : d61800 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53859, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1556 (p : Pattern) (ha : d53865 p = 1) (hb : d61360 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d61360 q = 1) : d61801 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1555 q ha hb
    | true =>
      simp only [d53860, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d61360 q = 1) : d61802 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d61360 q = 1) : d61803 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d61360 q = 1) : d61804 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d61360 q = 1) : d61805 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d61360 q = 1) : d61806 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1557 (p : Pattern) (ha : d61379 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61373 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d61374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d61374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d3329, d61374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d61375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d61375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d61375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61376 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61376, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61376, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61377 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61377, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61377, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61378 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61378, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61378, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61379 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61379, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61379, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1558 (p : Pattern) (ha : d61394 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d61388 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d61388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d3343, d61388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d61390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d61390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d61390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61391 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61391, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61391, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61392 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61392, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61392, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61393 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61393, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61393, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61394 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61394, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61394, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1559 (p : Pattern) (ha : d61400 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61370 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61380 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61380, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61380, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1557 q ha hb
  have h3 (q : Pattern) (ha : d61381 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61381, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61381, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61382 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61382, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61382, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61383 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61383, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61383, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61384 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61384, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61384, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61395 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61395, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61395, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1558 q ha hb
  have h8 (q : Pattern) (ha : d61396 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61396, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61396, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61397 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61397, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61397, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61398 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61398, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61398, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61399 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61399, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61399, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61400 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61400, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61400, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1560 (p : Pattern) (ha : d61410 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d61404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d61404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d3359, d61404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61405 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d61406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d61406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d61406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61407 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61407, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61407, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61408 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61408, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61408, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61409 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61409, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61409, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61410 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61410, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61410, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1561 (p : Pattern) (ha : d61416 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61411 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61411, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61411, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1560 q ha hb
  have h2 (q : Pattern) (ha : d61412 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61412, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61412, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61413 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61413, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61413, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61414 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61414, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61414, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61415 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61415, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61415, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61416 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61416, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61416, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1562 (p : Pattern) (ha : d61427 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61420 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d61421 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d61421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d3376, d61421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61422 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d61423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d61423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d61423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61424 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61424, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61424, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61425 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61425, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61425, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61426 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61426, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61426, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61427 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61427, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61427, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1563 (p : Pattern) (ha : d61433 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61428 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61428, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61428, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1562 q ha hb
  have h2 (q : Pattern) (ha : d61429 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61429, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61429, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61430 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61430, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61430, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61431 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61431, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61431, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61432 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61432, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61432, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61433 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61433, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61433, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1564 (p : Pattern) (ha : d61445 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d61439 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d61439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d3394, d61439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61440 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d61441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d61441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d61441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61442 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61442, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61442, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61443 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61443, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61443, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61444 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61444, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61444, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61445 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61445, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61445, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1565 (p : Pattern) (ha : d61451 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61446 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61446, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61446, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1564 q ha hb
  have h2 (q : Pattern) (ha : d61447 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61447, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61447, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61448 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61448, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61448, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61449 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61449, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61449, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61450 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61450, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61450, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61451 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61451, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61451, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1566 (p : Pattern) (ha : d61464 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d61458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d61458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d3413, d61458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61459 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d61460 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d61460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d61460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61461 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61461, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61461, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61462 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61462, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61462, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61463 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61463, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61463, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61464 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61464, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61464, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1567 (p : Pattern) (ha : d61470 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61465 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61465, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61465, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1566 q ha hb
  have h2 (q : Pattern) (ha : d61466 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61466, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61466, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61467 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61467, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61467, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61468 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61468, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61468, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61469 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61469, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61469, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61470 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61470, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61470, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1568 (p : Pattern) (ha : d61484 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61477 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d61478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d61478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d3433, d61478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61479 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d61480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d61480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d61480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61481 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61481, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61481, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d61482 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61482, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61482, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61483 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61483, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61483, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d61484 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61484, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61484, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro1569 (p : Pattern) (ha : d61490 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61485 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61485, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61485, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1568 q ha hb
  have h2 (q : Pattern) (ha : d61486 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61486, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61486, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61487 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61487, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61487, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61488 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61488, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61488, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61489 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61489, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61489, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61490 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61490, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61490, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1570 (p : Pattern) (ha : d61496 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61417 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61417, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1559 q ha hb
    | true =>
      simp only [d61417, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1561 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61434 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61434, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61434, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1563 q ha hb
  have h3 (q : Pattern) (ha : d61435 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61435, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61435, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61452 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61452, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61452, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1565 q ha hb
  have h5 (q : Pattern) (ha : d61453 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61453, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61453, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61454 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61454, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61454, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61471 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61471, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61471, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1567 q ha hb
  have h8 (q : Pattern) (ha : d61472 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61472, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61472, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61473 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61473, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61473, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61474 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61474, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61474, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61491 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61491, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61491, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1569 q ha hb
  have h12 (q : Pattern) (ha : d61492 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61492, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61492, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61493 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61493, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61493, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61494 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61494, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61494, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61495 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61495, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61495, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61496 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61496, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61496, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro1571 (p : Pattern) (ha : d61502 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61497 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61497, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1570 q ha hb
    | true =>
      simp only [d61497, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61498 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61498, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61498, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61499 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61499, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61499, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61500 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61500, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61500, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61501 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61501, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61501, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61502 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61502, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61502, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1572 (p : Pattern) (ha : d61508 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61503 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61503, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1571 q ha hb
    | true =>
      simp only [d61503, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61504 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61504, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61504, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61505 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61505, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61505, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61506 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61506, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61506, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61507 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61507, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61507, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61508 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61508, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61508, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1573 (p : Pattern) (ha : d61514 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61509 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61509, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1572 q ha hb
    | true =>
      simp only [d61509, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61510 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61510, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61510, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61511 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61511, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61511, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61512 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61512, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61512, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61513 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61513, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61513, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61514 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61514, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61514, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1574 (p : Pattern) (ha : d61520 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61515 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61515, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1573 q ha hb
    | true =>
      simp only [d61515, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61516 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61516, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61516, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61517 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61517, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61517, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61518 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61518, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61518, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61519 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61519, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61519, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61520 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61520, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61520, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1575 (p : Pattern) (ha : d61526 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61521 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61521, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1574 q ha hb
    | true =>
      simp only [d61521, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61522 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61522, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61522, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61523 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61523, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61523, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61524 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61524, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61524, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61525 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61525, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61525, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61526 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61526, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61526, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1576 (p : Pattern) (ha : d61532 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61527 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61527, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1575 q ha hb
    | true =>
      simp only [d61527, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61528 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61528, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61528, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61529 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61529, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61529, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61530 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61530, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61530, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61531 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61531, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61531, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61532 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61532, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61532, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1577 (p : Pattern) (ha : d61538 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61533 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61533, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1576 q ha hb
    | true =>
      simp only [d61533, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61534 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61534, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61534, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61535 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61535, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61535, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61536 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61536, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61536, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61537 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61537, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61537, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61538 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61538, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61538, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1578 (p : Pattern) (ha : d61544 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d3329, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d61540 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61541 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61541, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61541, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61542 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61542, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61542, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61543 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61543, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61543, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61544 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61544, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61544, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1579 (p : Pattern) (ha : d61555 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3345 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d3343, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3347 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d61551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61552 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61552, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61552, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61553 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61553, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61553, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61554 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61554, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61554, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61555 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61555, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61555, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1580 (p : Pattern) (ha : d61561 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61545 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61545, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61545, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1578 q ha hb
  have h3 (q : Pattern) (ha : d61546 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61546, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61546, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61547 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61547, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61547, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61548 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61548, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61548, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61549 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61549, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61549, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61556 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61556, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61556, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1579 q ha hb
  have h8 (q : Pattern) (ha : d61557 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61557, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61557, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61558 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61558, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61558, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61559 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61559, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61559, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61560 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61560, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61560, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61561 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61561, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61561, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1581 (p : Pattern) (ha : d61567 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3361 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d3359, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3363 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d61563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61564 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61564, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61564, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61565 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61565, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61565, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61566 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61566, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61566, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61567 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61567, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61567, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1582 (p : Pattern) (ha : d61573 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61568 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61568, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61568, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1581 q ha hb
  have h2 (q : Pattern) (ha : d61569 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61569, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61569, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61570 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61570, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61570, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61571 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61571, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61571, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61572 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61572, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61572, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61573 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61573, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61573, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1583 (p : Pattern) (ha : d61580 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d3376, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3380 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d61576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61577 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61577, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61577, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61578 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61578, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61578, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61579 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61579, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61579, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61580 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61580, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61580, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1584 (p : Pattern) (ha : d61586 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61581 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61581, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61581, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1583 q ha hb
  have h2 (q : Pattern) (ha : d61582 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61582, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61582, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61583 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61583, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61583, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61584 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61584, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61584, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61585 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61585, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61585, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61586 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61586, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61586, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1585 (p : Pattern) (ha : d61594 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3396 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d3394, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3398 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d61590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61591 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61591, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61591, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61592 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61592, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61592, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61593 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61593, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61593, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61594 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61594, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61594, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1586 (p : Pattern) (ha : d61600 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61595 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61595, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61595, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1585 q ha hb
  have h2 (q : Pattern) (ha : d61596 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61596, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61596, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61597 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61597, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61597, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61598 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61598, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61598, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61599 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61599, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61599, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61600 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61600, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61600, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1587 (p : Pattern) (ha : d61609 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d3413, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d61605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61606 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61606, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61606, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61607 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61607, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61607, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61608 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61608, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61608, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61609 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61609, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61609, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1588 (p : Pattern) (ha : d61615 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61610 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61610, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61610, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1587 q ha hb
  have h2 (q : Pattern) (ha : d61611 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61611, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61611, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61612 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61612, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61612, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61613 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61613, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61613, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61614 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61614, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61614, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61615 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61615, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61615, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1589 (p : Pattern) (ha : d61625 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3435 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d3433, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3437 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d61621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61622 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61622, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61622, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61623 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61623, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61623, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61624 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61624, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61624, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61625 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61625, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61625, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro1590 (p : Pattern) (ha : d61631 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61626 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61626, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61626, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1589 q ha hb
  have h2 (q : Pattern) (ha : d61627 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61627, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61627, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61628 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61628, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61628, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61629 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61629, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61629, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61630 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61630, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61630, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61631 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61631, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61631, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1591 (p : Pattern) (ha : d61637 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61574 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61574, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1580 q ha hb
    | true =>
      simp only [d61574, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1582 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61587 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61587, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61587, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1584 q ha hb
  have h3 (q : Pattern) (ha : d61588 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61588, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61588, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61601 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61601, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61601, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1586 q ha hb
  have h5 (q : Pattern) (ha : d61602 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61602, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61602, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61603 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61603, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61603, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61616 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61616, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61616, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1588 q ha hb
  have h8 (q : Pattern) (ha : d61617 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61617, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61617, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61618 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61618, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61618, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61619 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61619, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61619, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61632 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61632, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61632, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1590 q ha hb
  have h12 (q : Pattern) (ha : d61633 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61633, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61633, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61634 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61634, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61634, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61635 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61635, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61635, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61636 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61636, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61636, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61637 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61637, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61637, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1592 (p : Pattern) (ha : d61643 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61638 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61638, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1591 q ha hb
    | true =>
      simp only [d61638, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61639 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61639, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61639, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61640 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61640, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61640, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61641 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61641, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61641, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61642 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61642, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61642, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61643 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61643, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61643, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1593 (p : Pattern) (ha : d61649 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61644 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61644, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1592 q ha hb
    | true =>
      simp only [d61644, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61645 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61645, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61645, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61646 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61646, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61646, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61647 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61647, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61647, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61648 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61648, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61648, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61649 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61649, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61649, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1594 (p : Pattern) (ha : d61655 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61650 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61650, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1593 q ha hb
    | true =>
      simp only [d61650, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61651 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61651, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61651, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61652 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61652, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61652, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61653 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61653, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61653, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61654 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61654, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61654, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61655 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61655, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61655, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1595 (p : Pattern) (ha : d61661 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61656 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61656, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1594 q ha hb
    | true =>
      simp only [d61656, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61657 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61657, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61657, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61658 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61658, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61658, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61659 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61659, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61659, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61660 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61660, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61660, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61661 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61661, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61661, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1596 (p : Pattern) (ha : d61667 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61662 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61662, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1595 q ha hb
    | true =>
      simp only [d61662, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61663 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61663, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61663, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61664 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61664, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61664, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61665 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61665, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61665, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61666 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61666, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61666, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61667 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61667, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61667, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1597 (p : Pattern) (ha : d61673 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61668 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61668, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1596 q ha hb
    | true =>
      simp only [d61668, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61669 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61669, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61669, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61670 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61670, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61670, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61671 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61671, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61671, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61672 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61672, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61672, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61673 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61673, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61673, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1598 (p : Pattern) (ha : d61679 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61674 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61674, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1597 q ha hb
    | true =>
      simp only [d61674, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61675 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61675, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61675, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61676 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61676, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61676, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61677 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61677, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61677, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61678 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61678, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61678, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61679 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61679, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61679, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1599 (p : Pattern) (ha : d2672 p = 1) (hb : d61807 p = 1) : d3324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d48 q = 1) : d48 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d55 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d56 q = 1) (hb : d61357 q = 1) : d3319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d61357, d3319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d56, d61357, d3319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d57 q = 1) (hb : d61357 q = 1) : d3320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57, d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58 q = 1) (hb : d61357 q = 1) : d3321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58, d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d59 q = 1) (hb : d61357 q = 1) : d3322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d60 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d61 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d62 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d63 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d64 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d65 q = 1) (hb : d61357 q = 1) : d3323 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d65, d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d2672 q = 1) (hb : d61807 q = 1) : d3324 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2672, d61807, d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2672, d61807, d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1600 (p : Pattern) (ha : d54298 p = 1) (hb : d61807 p = 1) : d61544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d104 q = 1) : d104 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112 q = 1) (hb : d61357 q = 1) : d3329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113 q = 1) (hb : d61357 q = 1) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d114 q = 1) (hb : d61357 q = 1) : d3331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114, d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51643 q = 1) : d51643 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51647 q = 1) (hb : d61357 q = 1) : d61539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d61357, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51647, d61357, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d214 q = 1) (hb : d61357 q = 1) : d214 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d51648 q = 1) (hb : d61357 q = 1) : d61540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51648, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51649 q = 1) (hb : d61357 q = 1) : d61541 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51649, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d51650 q = 1) (hb : d61357 q = 1) : d61542 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51650, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4349 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4350 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4351 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4352 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h21 (q : Pattern) (ha : d4353 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d51651 q = 1) (hb : d61357 q = 1) : d61543 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51651, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d54298 q = 1) (hb : d61807 q = 1) : d61544 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54298, d61807, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d54298, d61807, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro1601 (p : Pattern) (ha : d54304 p = 1) (hb : d61807 p = 1) : d61555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d284 q = 1) : d284 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d291 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d292 q = 1) (hb : d61357 q = 1) : d3343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d293 q = 1) (hb : d61357 q = 1) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d294 q = 1) (hb : d61357 q = 1) : d3345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d294, d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51660 q = 1) : d51660 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51664 q = 1) (hb : d61357 q = 1) : d61550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d61357, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51664, d61357, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d397 q = 1) : d397 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d398 q = 1) (hb : d61357 q = 1) : d3347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d61357, d3347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d398, d61357, d3347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51665 q = 1) (hb : d61357 q = 1) : d61551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51665, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51666 q = 1) (hb : d61357 q = 1) : d61552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51666, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51667 q = 1) (hb : d61357 q = 1) : d61553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51667, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4385 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4386 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d407 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51668 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51669 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51670 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51671 q = 1) (hb : d61357 q = 1) : d61554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51671, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d54304 q = 1) (hb : d61807 q = 1) : d61555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54304, d61807, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d54304, d61807, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro1602 (p : Pattern) (ha : d54310 p = 1) (hb : d61807 p = 1) : d61561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2673 q = 1) (hb : d61807 q = 1) : d3325 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2673, d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2673, d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1599 q ha hb
  have h2 (q : Pattern) (ha : d2674 q = 1) (hb : d61807 q = 1) : d3326 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2674, d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2674, d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2675 q = 1) (hb : d61807 q = 1) : d3327 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2675, d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2675, d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2676 q = 1) (hb : d61807 q = 1) : d3328 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2676, d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2676, d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54299 q = 1) (hb : d61807 q = 1) : d61545 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54299, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54299, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1600 q ha hb
  have h6 (q : Pattern) (ha : d54300 q = 1) (hb : d61807 q = 1) : d61546 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54300, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54300, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54301 q = 1) (hb : d61807 q = 1) : d61547 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54301, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54301, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54302 q = 1) (hb : d61807 q = 1) : d61548 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54302, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54302, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54303 q = 1) (hb : d61807 q = 1) : d61549 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54303, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54303, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54305 q = 1) (hb : d61807 q = 1) : d61556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54305, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54305, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1601 q ha hb
  have h11 (q : Pattern) (ha : d54306 q = 1) (hb : d61807 q = 1) : d61557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54306, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54306, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54307 q = 1) (hb : d61807 q = 1) : d61558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54307, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54307, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54308 q = 1) (hb : d61807 q = 1) : d61559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54308, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54308, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54309 q = 1) (hb : d61807 q = 1) : d61560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54309, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54309, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54310 q = 1) (hb : d61807 q = 1) : d61561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54310, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54310, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1603 (p : Pattern) (ha : d54311 p = 1) (hb : d61807 p = 1) : d61567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d498 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d499 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d497 q = 1) : d497 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d507 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d508 q = 1) (hb : d61357 q = 1) : d3359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d509 q = 1) (hb : d61357 q = 1) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d510 q = 1) (hb : d61357 q = 1) : d3361 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d510, d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51685 q = 1) : d51685 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51689 q = 1) (hb : d61357 q = 1) : d61562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d61357, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51689, d61357, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d638 q = 1) : d638 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d644 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d645 q = 1) (hb : d61357 q = 1) : d3363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d61357, d3363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d645, d61357, d3363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51690 q = 1) (hb : d61357 q = 1) : d61563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51690, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51691 q = 1) (hb : d61357 q = 1) : d61564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51691, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51692 q = 1) (hb : d61357 q = 1) : d61565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51692, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4422 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4423 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d653 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d654 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51693 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51694 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51695 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51696 q = 1) (hb : d61357 q = 1) : d61566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51696, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d54311 q = 1) (hb : d61807 q = 1) : d61567 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54311, d61807, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d54311, d61807, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro1604 (p : Pattern) (ha : d54317 p = 1) (hb : d61807 p = 1) : d61573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54312 q = 1) (hb : d61807 q = 1) : d61568 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54312, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54312, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1603 q ha hb
  have h2 (q : Pattern) (ha : d54313 q = 1) (hb : d61807 q = 1) : d61569 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54313, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54313, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54314 q = 1) (hb : d61807 q = 1) : d61570 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54314, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54314, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54315 q = 1) (hb : d61807 q = 1) : d61571 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54315, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54315, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54316 q = 1) (hb : d61807 q = 1) : d61572 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54316, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54316, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54317 q = 1) (hb : d61807 q = 1) : d61573 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54317, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54317, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1605 (p : Pattern) (ha : d54319 p = 1) (hb : d61807 p = 1) : d61580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d790 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d791 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d789 q = 1) : d789 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d799 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d800 q = 1) (hb : d61357 q = 1) : d3376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d801 q = 1) (hb : d61357 q = 1) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d802 q = 1) (hb : d61357 q = 1) : d3378 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d802, d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51711 q = 1) : d51711 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51715 q = 1) (hb : d61357 q = 1) : d61575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d61357, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51715, d61357, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d944 q = 1) : d944 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d950 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d951 q = 1) (hb : d61357 q = 1) : d3380 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d61357, d3380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d951, d61357, d3380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51716 q = 1) (hb : d61357 q = 1) : d61576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51716, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51717 q = 1) (hb : d61357 q = 1) : d61577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51717, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51718 q = 1) (hb : d61357 q = 1) : d61578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51718, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4460 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4461 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d959 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d960 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51719 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51720 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51721 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51722 q = 1) (hb : d61357 q = 1) : d61579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51722, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d54319 q = 1) (hb : d61807 q = 1) : d61580 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54319, d61807, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d54319, d61807, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro1606 (p : Pattern) (ha : d54325 p = 1) (hb : d61807 p = 1) : d61586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54320 q = 1) (hb : d61807 q = 1) : d61581 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54320, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54320, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1605 q ha hb
  have h2 (q : Pattern) (ha : d54321 q = 1) (hb : d61807 q = 1) : d61582 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54321, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54321, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54322 q = 1) (hb : d61807 q = 1) : d61583 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54322, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54322, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54323 q = 1) (hb : d61807 q = 1) : d61584 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54323, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54323, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54324 q = 1) (hb : d61807 q = 1) : d61585 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54324, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54324, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54325 q = 1) (hb : d61807 q = 1) : d61586 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54325, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54325, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1607 (p : Pattern) (ha : d54328 p = 1) (hb : d61807 p = 1) : d61594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1169 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1170 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1168 q = 1) : d1168 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1178 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1179 q = 1) (hb : d61357 q = 1) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1180 q = 1) (hb : d61357 q = 1) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1181 q = 1) (hb : d61357 q = 1) : d3396 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1181, d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51738 q = 1) : d51738 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51742 q = 1) (hb : d61357 q = 1) : d61589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d61357, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51742, d61357, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d1355 q = 1) : d1355 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1361 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1362 q = 1) (hb : d61357 q = 1) : d3398 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d61357, d3398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d1362, d61357, d3398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51743 q = 1) (hb : d61357 q = 1) : d61590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51743, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51744 q = 1) (hb : d61357 q = 1) : d61591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51744, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51745 q = 1) (hb : d61357 q = 1) : d61592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51745, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4499 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4500 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d1370 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1371 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51746 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51747 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51748 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51749 q = 1) (hb : d61357 q = 1) : d61593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51749, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d54328 q = 1) (hb : d61807 q = 1) : d61594 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54328, d61807, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d54328, d61807, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro1608 (p : Pattern) (ha : d54334 p = 1) (hb : d61807 p = 1) : d61600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54329 q = 1) (hb : d61807 q = 1) : d61595 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54329, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54329, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1607 q ha hb
  have h2 (q : Pattern) (ha : d54330 q = 1) (hb : d61807 q = 1) : d61596 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54330, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54330, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54331 q = 1) (hb : d61807 q = 1) : d61597 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54331, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54331, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54332 q = 1) (hb : d61807 q = 1) : d61598 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54332, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54332, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54333 q = 1) (hb : d61807 q = 1) : d61599 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54333, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54333, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54334 q = 1) (hb : d61807 q = 1) : d61600 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54334, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54334, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1609 (p : Pattern) (ha : d54338 p = 1) (hb : d61807 p = 1) : d61609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1630 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1631 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1639 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1640 q = 1) (hb : d61357 q = 1) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1641 q = 1) (hb : d61357 q = 1) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1642 q = 1) (hb : d61357 q = 1) : d3415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1642, d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51766 q = 1) : d51766 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51770 q = 1) (hb : d61357 q = 1) : d61604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d61357, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51770, d61357, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d1832 q = 1) : d1832 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1838 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1839 q = 1) (hb : d61357 q = 1) : d3417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d61357, d3417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d1839, d61357, d3417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51771 q = 1) (hb : d61357 q = 1) : d61605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51771, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51772 q = 1) (hb : d61357 q = 1) : d61606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51772, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51773 q = 1) (hb : d61357 q = 1) : d61607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51773, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4539 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4540 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d1847 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1848 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51774 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51775 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51776 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51777 q = 1) (hb : d61357 q = 1) : d61608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51777, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d54338 q = 1) (hb : d61807 q = 1) : d61609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54338, d61807, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d54338, d61807, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro1610 (p : Pattern) (ha : d54344 p = 1) (hb : d61807 p = 1) : d61615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54339 q = 1) (hb : d61807 q = 1) : d61610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54339, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54339, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1609 q ha hb
  have h2 (q : Pattern) (ha : d54340 q = 1) (hb : d61807 q = 1) : d61611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54340, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54340, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54341 q = 1) (hb : d61807 q = 1) : d61612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54341, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54341, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54342 q = 1) (hb : d61807 q = 1) : d61613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54342, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54342, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54343 q = 1) (hb : d61807 q = 1) : d61614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54343, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54343, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54344 q = 1) (hb : d61807 q = 1) : d61615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54344, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54344, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1611 (p : Pattern) (ha : d54349 p = 1) (hb : d61807 p = 1) : d61625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2113 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2114 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2122 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2123 q = 1) (hb : d61357 q = 1) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2124 q = 1) (hb : d61357 q = 1) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2125 q = 1) (hb : d61357 q = 1) : d3435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2125, d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51795 q = 1) : d51795 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51799 q = 1) (hb : d61357 q = 1) : d61620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d61357, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51799, d61357, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d2310 q = 1) : d2310 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2316 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d2317 q = 1) (hb : d61357 q = 1) : d3437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d61357, d3437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d2317, d61357, d3437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51800 q = 1) (hb : d61357 q = 1) : d61621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51800, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51801 q = 1) (hb : d61357 q = 1) : d61622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51801, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51802 q = 1) (hb : d61357 q = 1) : d61623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51802, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4580 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4581 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d2325 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d2326 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51803 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51804 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51805 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51806 q = 1) (hb : d61357 q = 1) : d61624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51806, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d54349 q = 1) (hb : d61807 q = 1) : d61625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54349, d61807, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d54349, d61807, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro1612 (p : Pattern) (ha : d54355 p = 1) (hb : d61807 p = 1) : d61631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54350 q = 1) (hb : d61807 q = 1) : d61626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54350, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54350, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1611 q ha hb
  have h2 (q : Pattern) (ha : d54351 q = 1) (hb : d61807 q = 1) : d61627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54351, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54351, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54352 q = 1) (hb : d61807 q = 1) : d61628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54352, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54352, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54353 q = 1) (hb : d61807 q = 1) : d61629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54353, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54353, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54354 q = 1) (hb : d61807 q = 1) : d61630 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54354, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54354, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54355 q = 1) (hb : d61807 q = 1) : d61631 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54355, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54355, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1613 (p : Pattern) (ha : d54361 p = 1) (hb : d61807 p = 1) : d61637 p = 1 := by
  have h0 (q : Pattern) (ha : d54318 q = 1) (hb : d61807 q = 1) : d61574 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54318, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1602 q ha hb
    | true =>
      simp only [d54318, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1604 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54326 q = 1) (hb : d61807 q = 1) : d61587 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54326, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54326, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1606 q ha hb
  have h3 (q : Pattern) (ha : d54327 q = 1) (hb : d61807 q = 1) : d61588 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54327, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54327, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54335 q = 1) (hb : d61807 q = 1) : d61601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54335, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54335, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1608 q ha hb
  have h5 (q : Pattern) (ha : d54336 q = 1) (hb : d61807 q = 1) : d61602 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54336, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54336, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54337 q = 1) (hb : d61807 q = 1) : d61603 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54337, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54337, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54345 q = 1) (hb : d61807 q = 1) : d61616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54345, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54345, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1610 q ha hb
  have h8 (q : Pattern) (ha : d54346 q = 1) (hb : d61807 q = 1) : d61617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54346, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54346, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54347 q = 1) (hb : d61807 q = 1) : d61618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54347, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54347, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54348 q = 1) (hb : d61807 q = 1) : d61619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54348, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54348, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54356 q = 1) (hb : d61807 q = 1) : d61632 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54356, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54356, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1612 q ha hb
  have h12 (q : Pattern) (ha : d54357 q = 1) (hb : d61807 q = 1) : d61633 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54357, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54357, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54358 q = 1) (hb : d61807 q = 1) : d61634 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54358, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54358, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54359 q = 1) (hb : d61807 q = 1) : d61635 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54359, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54359, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54360 q = 1) (hb : d61807 q = 1) : d61636 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54360, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54360, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54361 q = 1) (hb : d61807 q = 1) : d61637 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54361, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54361, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1614 (p : Pattern) (ha : d54367 p = 1) (hb : d61807 p = 1) : d61643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54362 q = 1) (hb : d61807 q = 1) : d61638 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54362, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1613 q ha hb
    | true =>
      simp only [d54362, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54363 q = 1) (hb : d61807 q = 1) : d61639 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54363, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54363, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54364 q = 1) (hb : d61807 q = 1) : d61640 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54364, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54364, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54365 q = 1) (hb : d61807 q = 1) : d61641 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54365, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54365, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54366 q = 1) (hb : d61807 q = 1) : d61642 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54366, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54366, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54367 q = 1) (hb : d61807 q = 1) : d61643 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54367, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54367, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1615 (p : Pattern) (ha : d54373 p = 1) (hb : d61807 p = 1) : d61649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54368 q = 1) (hb : d61807 q = 1) : d61644 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54368, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1614 q ha hb
    | true =>
      simp only [d54368, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54369 q = 1) (hb : d61807 q = 1) : d61645 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54369, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54369, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54370 q = 1) (hb : d61807 q = 1) : d61646 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54370, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54370, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54371 q = 1) (hb : d61807 q = 1) : d61647 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54371, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54371, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54372 q = 1) (hb : d61807 q = 1) : d61648 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54372, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54372, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54373 q = 1) (hb : d61807 q = 1) : d61649 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54373, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54373, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1616 (p : Pattern) (ha : d54379 p = 1) (hb : d61807 p = 1) : d61655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54374 q = 1) (hb : d61807 q = 1) : d61650 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54374, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1615 q ha hb
    | true =>
      simp only [d54374, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54375 q = 1) (hb : d61807 q = 1) : d61651 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54375, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54375, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54376 q = 1) (hb : d61807 q = 1) : d61652 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54376, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54376, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54377 q = 1) (hb : d61807 q = 1) : d61653 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54377, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54377, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54378 q = 1) (hb : d61807 q = 1) : d61654 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54378, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54378, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54379 q = 1) (hb : d61807 q = 1) : d61655 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54379, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54379, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1617 (p : Pattern) (ha : d54385 p = 1) (hb : d61807 p = 1) : d61661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54380 q = 1) (hb : d61807 q = 1) : d61656 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54380, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1616 q ha hb
    | true =>
      simp only [d54380, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54381 q = 1) (hb : d61807 q = 1) : d61657 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54381, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54381, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54382 q = 1) (hb : d61807 q = 1) : d61658 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54382, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54382, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54383 q = 1) (hb : d61807 q = 1) : d61659 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54383, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54383, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54384 q = 1) (hb : d61807 q = 1) : d61660 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54384, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54384, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54385 q = 1) (hb : d61807 q = 1) : d61661 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54385, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54385, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1618 (p : Pattern) (ha : d54391 p = 1) (hb : d61807 p = 1) : d61667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54386 q = 1) (hb : d61807 q = 1) : d61662 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54386, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1617 q ha hb
    | true =>
      simp only [d54386, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54387 q = 1) (hb : d61807 q = 1) : d61663 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54387, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54387, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54388 q = 1) (hb : d61807 q = 1) : d61664 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54388, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54388, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54389 q = 1) (hb : d61807 q = 1) : d61665 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54389, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54389, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54390 q = 1) (hb : d61807 q = 1) : d61666 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54390, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54390, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54391 q = 1) (hb : d61807 q = 1) : d61667 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54391, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54391, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1619 (p : Pattern) (ha : d54397 p = 1) (hb : d61807 p = 1) : d61673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54392 q = 1) (hb : d61807 q = 1) : d61668 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54392, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1618 q ha hb
    | true =>
      simp only [d54392, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54393 q = 1) (hb : d61807 q = 1) : d61669 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54393, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54393, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54394 q = 1) (hb : d61807 q = 1) : d61670 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54394, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54394, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54395 q = 1) (hb : d61807 q = 1) : d61671 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54395, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54395, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54396 q = 1) (hb : d61807 q = 1) : d61672 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54396, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54396, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54397 q = 1) (hb : d61807 q = 1) : d61673 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54397, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54397, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1620 (p : Pattern) (ha : d54403 p = 1) (hb : d61807 p = 1) : d61679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54398 q = 1) (hb : d61807 q = 1) : d61674 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54398, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1619 q ha hb
    | true =>
      simp only [d54398, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54399 q = 1) (hb : d61807 q = 1) : d61675 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54399, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54399, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54400 q = 1) (hb : d61807 q = 1) : d61676 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54400, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54400, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54401 q = 1) (hb : d61807 q = 1) : d61677 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54401, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54401, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54402 q = 1) (hb : d61807 q = 1) : d61678 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54402, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54402, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54403 q = 1) (hb : d61807 q = 1) : d61679 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54403, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54403, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1621 (p : Pattern) (ha : d54404 p = 1) (hb : d61807 p = 1) : d61683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d104 q = 1) : d104 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d61357 q = 1) : d3329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d61357 q = 1) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d61357 q = 1) : d61680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53637, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d61357 q = 1) : d61681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d407 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53639 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53640 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53641 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53642 q = 1) (hb : d61357 q = 1) : d61682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54404 q = 1) (hb : d61807 q = 1) : d61683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54404, d61807, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54404, d61807, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1622 (p : Pattern) (ha : d54410 p = 1) (hb : d61807 p = 1) : d61692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d284 q = 1) : d284 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d61357 q = 1) : d3343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d61357 q = 1) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53653 q = 1) (hb : d61357 q = 1) : d61689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53653, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d61357 q = 1) : d61690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53655 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53656 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53656, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53657 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53658 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53659 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53660 q = 1) (hb : d61357 q = 1) : d61691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53660, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54410 q = 1) (hb : d61807 q = 1) : d61692 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54410, d61807, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54410, d61807, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1623 (p : Pattern) (ha : d54416 p = 1) (hb : d61807 p = 1) : d61698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54405 q = 1) (hb : d61807 q = 1) : d61684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54405, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54405, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1621 q ha hb
  have h2 (q : Pattern) (ha : d54406 q = 1) (hb : d61807 q = 1) : d61685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54406, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54406, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54407 q = 1) (hb : d61807 q = 1) : d61686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54407, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54407, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54408 q = 1) (hb : d61807 q = 1) : d61687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54408, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54408, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54409 q = 1) (hb : d61807 q = 1) : d61688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54409, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54409, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54411 q = 1) (hb : d61807 q = 1) : d61693 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54411, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54411, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1622 q ha hb
  have h7 (q : Pattern) (ha : d54412 q = 1) (hb : d61807 q = 1) : d61694 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54412, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54412, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54413 q = 1) (hb : d61807 q = 1) : d61695 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54413, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54413, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54414 q = 1) (hb : d61807 q = 1) : d61696 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54414, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54414, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54415 q = 1) (hb : d61807 q = 1) : d61697 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54415, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54415, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54416 q = 1) (hb : d61807 q = 1) : d61698 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54416, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54416, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro1624 (p : Pattern) (ha : d54417 p = 1) (hb : d61807 p = 1) : d61702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d497 q = 1) : d497 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d507 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d61357 q = 1) : d3359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d61357 q = 1) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53678 q = 1) (hb : d61357 q = 1) : d61699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53678, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d61357 q = 1) : d61700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53680 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53681 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53681, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53682 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53683 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53684 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53685 q = 1) (hb : d61357 q = 1) : d61701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53685, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54417 q = 1) (hb : d61807 q = 1) : d61702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54417, d61807, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54417, d61807, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1625 (p : Pattern) (ha : d54423 p = 1) (hb : d61807 p = 1) : d61708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54418 q = 1) (hb : d61807 q = 1) : d61703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54418, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54418, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1624 q ha hb
  have h2 (q : Pattern) (ha : d54419 q = 1) (hb : d61807 q = 1) : d61704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54419, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54419, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54420 q = 1) (hb : d61807 q = 1) : d61705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54420, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54420, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54421 q = 1) (hb : d61807 q = 1) : d61706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54421, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54421, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54422 q = 1) (hb : d61807 q = 1) : d61707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54422, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54422, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54423 q = 1) (hb : d61807 q = 1) : d61708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54423, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54423, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1626 (p : Pattern) (ha : d54425 p = 1) (hb : d61807 p = 1) : d61713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d789 q = 1) : d789 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d799 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d61357 q = 1) : d3376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d61357 q = 1) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53705 q = 1) (hb : d61357 q = 1) : d61710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53705, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d61357 q = 1) : d61711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53707 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53708 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53708, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53709 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53710 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53711 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53712 q = 1) (hb : d61357 q = 1) : d61712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53712, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54425 q = 1) (hb : d61807 q = 1) : d61713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54425, d61807, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54425, d61807, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1627 (p : Pattern) (ha : d54431 p = 1) (hb : d61807 p = 1) : d61719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54426 q = 1) (hb : d61807 q = 1) : d61714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54426, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54426, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1626 q ha hb
  have h2 (q : Pattern) (ha : d54427 q = 1) (hb : d61807 q = 1) : d61715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54427, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54427, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54428 q = 1) (hb : d61807 q = 1) : d61716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54428, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54428, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54429 q = 1) (hb : d61807 q = 1) : d61717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54429, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54429, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54430 q = 1) (hb : d61807 q = 1) : d61718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54430, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54430, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54431 q = 1) (hb : d61807 q = 1) : d61719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54431, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54431, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1628 (p : Pattern) (ha : d54434 p = 1) (hb : d61807 p = 1) : d61725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1168 q = 1) : d1168 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d61357 q = 1) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d61357 q = 1) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53733 q = 1) (hb : d61357 q = 1) : d61722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53733, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d61357 q = 1) : d61723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53735 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53736 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53736, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53737 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53738 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53739 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53740 q = 1) (hb : d61357 q = 1) : d61724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53740, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54434 q = 1) (hb : d61807 q = 1) : d61725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54434, d61807, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54434, d61807, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1629 (p : Pattern) (ha : d54440 p = 1) (hb : d61807 p = 1) : d61731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54435 q = 1) (hb : d61807 q = 1) : d61726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54435, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54435, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1628 q ha hb
  have h2 (q : Pattern) (ha : d54436 q = 1) (hb : d61807 q = 1) : d61727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54436, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54436, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54437 q = 1) (hb : d61807 q = 1) : d61728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54437, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54437, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54438 q = 1) (hb : d61807 q = 1) : d61729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54438, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54438, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54439 q = 1) (hb : d61807 q = 1) : d61730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54439, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54439, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54440 q = 1) (hb : d61807 q = 1) : d61731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54440, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54440, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1630 (p : Pattern) (ha : d54444 p = 1) (hb : d61807 p = 1) : d61738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d61357 q = 1) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d61357 q = 1) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d61357 q = 1) : d61735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53762, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d61357 q = 1) : d61736 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53764 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53765 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53765, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53766 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53767 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53768 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53769 q = 1) (hb : d61357 q = 1) : d61737 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53769, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54444 q = 1) (hb : d61807 q = 1) : d61738 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54444, d61807, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54444, d61807, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1631 (p : Pattern) (ha : d54450 p = 1) (hb : d61807 p = 1) : d61744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54445 q = 1) (hb : d61807 q = 1) : d61739 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54445, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54445, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1630 q ha hb
  have h2 (q : Pattern) (ha : d54446 q = 1) (hb : d61807 q = 1) : d61740 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54446, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54446, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54447 q = 1) (hb : d61807 q = 1) : d61741 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54447, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54447, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54448 q = 1) (hb : d61807 q = 1) : d61742 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54448, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54448, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54449 q = 1) (hb : d61807 q = 1) : d61743 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54449, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54449, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54450 q = 1) (hb : d61807 q = 1) : d61744 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54450, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54450, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1632 (p : Pattern) (ha : d54455 p = 1) (hb : d61807 p = 1) : d61752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d61357 q = 1) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d61357 q = 1) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d61357 q = 1) : d61749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53792, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d61357 q = 1) : d61750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53794 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53795 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53795, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53796 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53797 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53798 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53799 q = 1) (hb : d61357 q = 1) : d61751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53799, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d54455 q = 1) (hb : d61807 q = 1) : d61752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54455, d61807, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54455, d61807, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1633 (p : Pattern) (ha : d54461 p = 1) (hb : d61807 p = 1) : d61758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54456 q = 1) (hb : d61807 q = 1) : d61753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54456, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54456, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1632 q ha hb
  have h2 (q : Pattern) (ha : d54457 q = 1) (hb : d61807 q = 1) : d61754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54457, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54457, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54458 q = 1) (hb : d61807 q = 1) : d61755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54458, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54458, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54459 q = 1) (hb : d61807 q = 1) : d61756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54459, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54459, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54460 q = 1) (hb : d61807 q = 1) : d61757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54460, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54460, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54461 q = 1) (hb : d61807 q = 1) : d61758 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54461, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54461, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1634 (p : Pattern) (ha : d54467 p = 1) (hb : d61807 p = 1) : d61764 p = 1 := by
  have h0 (q : Pattern) (ha : d54424 q = 1) (hb : d61807 q = 1) : d61709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54424, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1623 q ha hb
    | true =>
      simp only [d54424, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1625 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54432 q = 1) (hb : d61807 q = 1) : d61720 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54432, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54432, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1627 q ha hb
  have h3 (q : Pattern) (ha : d54433 q = 1) (hb : d61807 q = 1) : d61721 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54433, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54433, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54441 q = 1) (hb : d61807 q = 1) : d61732 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54441, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54441, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1629 q ha hb
  have h5 (q : Pattern) (ha : d54442 q = 1) (hb : d61807 q = 1) : d61733 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54442, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54442, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54443 q = 1) (hb : d61807 q = 1) : d61734 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54443, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54443, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54451 q = 1) (hb : d61807 q = 1) : d61745 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54451, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54451, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1631 q ha hb
  have h8 (q : Pattern) (ha : d54452 q = 1) (hb : d61807 q = 1) : d61746 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54452, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54452, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54453 q = 1) (hb : d61807 q = 1) : d61747 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54453, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54453, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54454 q = 1) (hb : d61807 q = 1) : d61748 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54454, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54454, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54462 q = 1) (hb : d61807 q = 1) : d61759 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54462, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54462, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1633 q ha hb
  have h12 (q : Pattern) (ha : d54463 q = 1) (hb : d61807 q = 1) : d61760 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54463, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54463, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54464 q = 1) (hb : d61807 q = 1) : d61761 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54464, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54464, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54465 q = 1) (hb : d61807 q = 1) : d61762 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54465, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54465, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54466 q = 1) (hb : d61807 q = 1) : d61763 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54466, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54466, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54467 q = 1) (hb : d61807 q = 1) : d61764 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54467, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54467, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1635 (p : Pattern) (ha : d54473 p = 1) (hb : d61807 p = 1) : d61770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54468 q = 1) (hb : d61807 q = 1) : d61765 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54468, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1634 q ha hb
    | true =>
      simp only [d54468, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54469 q = 1) (hb : d61807 q = 1) : d61766 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54469, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54469, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54470 q = 1) (hb : d61807 q = 1) : d61767 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54470, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54470, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54471 q = 1) (hb : d61807 q = 1) : d61768 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54471, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54471, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54472 q = 1) (hb : d61807 q = 1) : d61769 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54472, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54472, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54473 q = 1) (hb : d61807 q = 1) : d61770 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54473, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54473, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1636 (p : Pattern) (ha : d54479 p = 1) (hb : d61807 p = 1) : d61776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54474 q = 1) (hb : d61807 q = 1) : d61771 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54474, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1635 q ha hb
    | true =>
      simp only [d54474, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54475 q = 1) (hb : d61807 q = 1) : d61772 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54475, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54475, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54476 q = 1) (hb : d61807 q = 1) : d61773 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54476, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54476, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54477 q = 1) (hb : d61807 q = 1) : d61774 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54477, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54477, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54478 q = 1) (hb : d61807 q = 1) : d61775 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54478, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54478, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54479 q = 1) (hb : d61807 q = 1) : d61776 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54479, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54479, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1637 (p : Pattern) (ha : d54485 p = 1) (hb : d61807 p = 1) : d61782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54480 q = 1) (hb : d61807 q = 1) : d61777 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54480, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1636 q ha hb
    | true =>
      simp only [d54480, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54481 q = 1) (hb : d61807 q = 1) : d61778 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54481, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54481, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54482 q = 1) (hb : d61807 q = 1) : d61779 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54482, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54482, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54483 q = 1) (hb : d61807 q = 1) : d61780 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54483, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54483, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54484 q = 1) (hb : d61807 q = 1) : d61781 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54484, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54484, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54485 q = 1) (hb : d61807 q = 1) : d61782 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54485, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54485, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1638 (p : Pattern) (ha : d54491 p = 1) (hb : d61807 p = 1) : d61788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54486 q = 1) (hb : d61807 q = 1) : d61783 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54486, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1637 q ha hb
    | true =>
      simp only [d54486, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54487 q = 1) (hb : d61807 q = 1) : d61784 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54487, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54487, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54488 q = 1) (hb : d61807 q = 1) : d61785 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54488, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54488, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54489 q = 1) (hb : d61807 q = 1) : d61786 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54489, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54489, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54490 q = 1) (hb : d61807 q = 1) : d61787 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54490, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54490, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54491 q = 1) (hb : d61807 q = 1) : d61788 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54491, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54491, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1639 (p : Pattern) (ha : d54497 p = 1) (hb : d61807 p = 1) : d61794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54492 q = 1) (hb : d61807 q = 1) : d61789 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54492, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1638 q ha hb
    | true =>
      simp only [d54492, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54493 q = 1) (hb : d61807 q = 1) : d61790 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54493, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54493, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54494 q = 1) (hb : d61807 q = 1) : d61791 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54494, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54494, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54495 q = 1) (hb : d61807 q = 1) : d61792 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54495, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54495, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54496 q = 1) (hb : d61807 q = 1) : d61793 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54496, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54496, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54497 q = 1) (hb : d61807 q = 1) : d61794 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54497, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54497, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1640 (p : Pattern) (ha : d54503 p = 1) (hb : d61807 p = 1) : d61800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54498 q = 1) (hb : d61807 q = 1) : d61795 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54498, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1639 q ha hb
    | true =>
      simp only [d54498, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54499 q = 1) (hb : d61807 q = 1) : d61796 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54499, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54499, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54500 q = 1) (hb : d61807 q = 1) : d61797 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54500, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54500, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54501 q = 1) (hb : d61807 q = 1) : d61798 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54501, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54501, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54502 q = 1) (hb : d61807 q = 1) : d61799 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54502, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54502, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54503 q = 1) (hb : d61807 q = 1) : d61800 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54503, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54503, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1641 (p : Pattern) (ha : d54509 p = 1) (hb : d61807 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54504 q = 1) (hb : d61807 q = 1) : d61801 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54504, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1640 q ha hb
    | true =>
      simp only [d54504, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54505 q = 1) (hb : d61807 q = 1) : d61802 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54505, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54505, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54506 q = 1) (hb : d61807 q = 1) : d61803 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54506, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54506, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54507 q = 1) (hb : d61807 q = 1) : d61804 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54507, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54507, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54508 q = 1) (hb : d61807 q = 1) : d61805 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54508, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54508, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54509 q = 1) (hb : d61807 q = 1) : d61806 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54509, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54509, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1642 (p : Pattern) (ha : d2672 p = 1) (hb : d55878 p = 1) : d2520 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d59 q = 1) : d59 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d65 q = 1) (hb : d54517 q = 1) : d2519 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, d54517, d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d65, d54517, d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2672 q = 1) (hb : d55878 q = 1) : d2520 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2672, d55878, d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2672, d55878, d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1643 (p : Pattern) (ha : d54298 p = 1) (hb : d55878 p = 1) : d54752 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51650 q = 1) : d51650 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51651 q = 1) (hb : d54517 q = 1) : d54751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d54517, d54751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51651, d54517, d54751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54298 q = 1) (hb : d55878 q = 1) : d54752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54298, d55878, d54752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54298, d55878, d54752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1644 (p : Pattern) (ha : d54304 p = 1) (hb : d55878 p = 1) : d54759 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51667 q = 1) : d51667 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51671 q = 1) (hb : d54517 q = 1) : d54758 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d54517, d54758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51671, d54517, d54758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54304 q = 1) (hb : d55878 q = 1) : d54759 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54304, d55878, d54759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54304, d55878, d54759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1645 (p : Pattern) (ha : d54310 p = 1) (hb : d55878 p = 1) : d54765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2673 q = 1) (hb : d55878 q = 1) : d2521 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2673, d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2673, d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1642 q ha hb
  have h2 (q : Pattern) (ha : d2674 q = 1) (hb : d55878 q = 1) : d2522 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2674, d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2674, d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2675 q = 1) (hb : d55878 q = 1) : d2523 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2675, d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2675, d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2676 q = 1) (hb : d55878 q = 1) : d2524 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2676, d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2676, d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54299 q = 1) (hb : d55878 q = 1) : d54753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54299, d54753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54299, d54753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1643 q ha hb
  have h6 (q : Pattern) (ha : d54300 q = 1) (hb : d55878 q = 1) : d54754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54300, d54754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54300, d54754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54301 q = 1) (hb : d55878 q = 1) : d54755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54301, d54755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54301, d54755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54302 q = 1) (hb : d55878 q = 1) : d54756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54302, d54756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54302, d54756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54303 q = 1) (hb : d55878 q = 1) : d54757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54303, d54757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54303, d54757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54305 q = 1) (hb : d55878 q = 1) : d54760 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54305, d54760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54305, d54760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1644 q ha hb
  have h11 (q : Pattern) (ha : d54306 q = 1) (hb : d55878 q = 1) : d54761 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54306, d54761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54306, d54761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54307 q = 1) (hb : d55878 q = 1) : d54762 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54307, d54762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54307, d54762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54308 q = 1) (hb : d55878 q = 1) : d54763 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54308, d54763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54308, d54763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54309 q = 1) (hb : d55878 q = 1) : d54764 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54309, d54764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54309, d54764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54310 q = 1) (hb : d55878 q = 1) : d54765 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54310, d54765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54310, d54765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1646 (p : Pattern) (ha : d54311 p = 1) (hb : d55878 p = 1) : d54767 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51692 q = 1) : d51692 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51696 q = 1) (hb : d54517 q = 1) : d54766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d54517, d54766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51696, d54517, d54766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54311 q = 1) (hb : d55878 q = 1) : d54767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54311, d55878, d54767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54311, d55878, d54767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1647 (p : Pattern) (ha : d54317 p = 1) (hb : d55878 p = 1) : d54773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54312 q = 1) (hb : d55878 q = 1) : d54768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54312, d54768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54312, d54768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1646 q ha hb
  have h2 (q : Pattern) (ha : d54313 q = 1) (hb : d55878 q = 1) : d54769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54313, d54769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54313, d54769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54314 q = 1) (hb : d55878 q = 1) : d54770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54314, d54770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54314, d54770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54315 q = 1) (hb : d55878 q = 1) : d54771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54315, d54771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54315, d54771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54316 q = 1) (hb : d55878 q = 1) : d54772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54316, d54772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54316, d54772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54317 q = 1) (hb : d55878 q = 1) : d54773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54317, d54773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54317, d54773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1648 (p : Pattern) (ha : d54319 p = 1) (hb : d55878 p = 1) : d54776 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51718 q = 1) : d51718 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51722 q = 1) (hb : d54517 q = 1) : d54775 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d54517, d54775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51722, d54517, d54775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54319 q = 1) (hb : d55878 q = 1) : d54776 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54319, d55878, d54776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54319, d55878, d54776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1649 (p : Pattern) (ha : d54325 p = 1) (hb : d55878 p = 1) : d54782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54320 q = 1) (hb : d55878 q = 1) : d54777 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54320, d54777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54320, d54777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1648 q ha hb
  have h2 (q : Pattern) (ha : d54321 q = 1) (hb : d55878 q = 1) : d54778 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54321, d54778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54321, d54778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54322 q = 1) (hb : d55878 q = 1) : d54779 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54322, d54779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54322, d54779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54323 q = 1) (hb : d55878 q = 1) : d54780 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54323, d54780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54323, d54780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54324 q = 1) (hb : d55878 q = 1) : d54781 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54324, d54781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54324, d54781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54325 q = 1) (hb : d55878 q = 1) : d54782 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54325, d54782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54325, d54782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1650 (p : Pattern) (ha : d54328 p = 1) (hb : d55878 p = 1) : d54786 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51745 q = 1) : d51745 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51749 q = 1) (hb : d54517 q = 1) : d54785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d54517, d54785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51749, d54517, d54785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54328 q = 1) (hb : d55878 q = 1) : d54786 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54328, d55878, d54786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54328, d55878, d54786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1651 (p : Pattern) (ha : d54334 p = 1) (hb : d55878 p = 1) : d54792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54329 q = 1) (hb : d55878 q = 1) : d54787 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54329, d54787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54329, d54787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1650 q ha hb
  have h2 (q : Pattern) (ha : d54330 q = 1) (hb : d55878 q = 1) : d54788 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54330, d54788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54330, d54788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54331 q = 1) (hb : d55878 q = 1) : d54789 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54331, d54789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54331, d54789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54332 q = 1) (hb : d55878 q = 1) : d54790 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54332, d54790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54332, d54790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54333 q = 1) (hb : d55878 q = 1) : d54791 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54333, d54791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54333, d54791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54334 q = 1) (hb : d55878 q = 1) : d54792 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54334, d54792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54334, d54792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1652 (p : Pattern) (ha : d54338 p = 1) (hb : d55878 p = 1) : d54797 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51773 q = 1) : d51773 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51777 q = 1) (hb : d54517 q = 1) : d54796 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d54517, d54796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51777, d54517, d54796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54338 q = 1) (hb : d55878 q = 1) : d54797 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54338, d55878, d54797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54338, d55878, d54797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1653 (p : Pattern) (ha : d54344 p = 1) (hb : d55878 p = 1) : d54803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54339 q = 1) (hb : d55878 q = 1) : d54798 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54339, d54798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54339, d54798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1652 q ha hb
  have h2 (q : Pattern) (ha : d54340 q = 1) (hb : d55878 q = 1) : d54799 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54340, d54799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54340, d54799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54341 q = 1) (hb : d55878 q = 1) : d54800 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54341, d54800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54341, d54800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54342 q = 1) (hb : d55878 q = 1) : d54801 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54342, d54801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54342, d54801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54343 q = 1) (hb : d55878 q = 1) : d54802 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54343, d54802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54343, d54802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54344 q = 1) (hb : d55878 q = 1) : d54803 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54344, d54803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54344, d54803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1654 (p : Pattern) (ha : d54349 p = 1) (hb : d55878 p = 1) : d54809 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51802 q = 1) : d51802 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51806 q = 1) (hb : d54517 q = 1) : d54808 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d54517, d54808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51806, d54517, d54808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54349 q = 1) (hb : d55878 q = 1) : d54809 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54349, d55878, d54809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54349, d55878, d54809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1655 (p : Pattern) (ha : d54355 p = 1) (hb : d55878 p = 1) : d54815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54350 q = 1) (hb : d55878 q = 1) : d54810 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54350, d54810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54350, d54810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1654 q ha hb
  have h2 (q : Pattern) (ha : d54351 q = 1) (hb : d55878 q = 1) : d54811 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54351, d54811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54351, d54811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54352 q = 1) (hb : d55878 q = 1) : d54812 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54352, d54812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54352, d54812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54353 q = 1) (hb : d55878 q = 1) : d54813 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54353, d54813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54353, d54813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54354 q = 1) (hb : d55878 q = 1) : d54814 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54354, d54814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54354, d54814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54355 q = 1) (hb : d55878 q = 1) : d54815 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54355, d54815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54355, d54815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1656 (p : Pattern) (ha : d54361 p = 1) (hb : d55878 p = 1) : d54821 p = 1 := by
  have h0 (q : Pattern) (ha : d54318 q = 1) (hb : d55878 q = 1) : d54774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54318, d54774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1645 q ha hb
    | true =>
      simp only [d54318, d54774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1647 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54326 q = 1) (hb : d55878 q = 1) : d54783 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54326, d54783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54326, d54783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1649 q ha hb
  have h3 (q : Pattern) (ha : d54327 q = 1) (hb : d55878 q = 1) : d54784 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54327, d54784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54327, d54784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54335 q = 1) (hb : d55878 q = 1) : d54793 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54335, d54793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54335, d54793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1651 q ha hb
  have h5 (q : Pattern) (ha : d54336 q = 1) (hb : d55878 q = 1) : d54794 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54336, d54794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54336, d54794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54337 q = 1) (hb : d55878 q = 1) : d54795 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54337, d54795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54337, d54795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54345 q = 1) (hb : d55878 q = 1) : d54804 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54345, d54804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54345, d54804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1653 q ha hb
  have h8 (q : Pattern) (ha : d54346 q = 1) (hb : d55878 q = 1) : d54805 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54346, d54805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54346, d54805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54347 q = 1) (hb : d55878 q = 1) : d54806 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54347, d54806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54347, d54806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54348 q = 1) (hb : d55878 q = 1) : d54807 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54348, d54807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54348, d54807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54356 q = 1) (hb : d55878 q = 1) : d54816 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54356, d54816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54356, d54816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1655 q ha hb
  have h12 (q : Pattern) (ha : d54357 q = 1) (hb : d55878 q = 1) : d54817 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54357, d54817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54357, d54817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54358 q = 1) (hb : d55878 q = 1) : d54818 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54358, d54818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54358, d54818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54359 q = 1) (hb : d55878 q = 1) : d54819 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54359, d54819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54359, d54819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54360 q = 1) (hb : d55878 q = 1) : d54820 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54360, d54820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54360, d54820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54361 q = 1) (hb : d55878 q = 1) : d54821 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54361, d54821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54361, d54821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1657 (p : Pattern) (ha : d54367 p = 1) (hb : d55878 p = 1) : d54827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54362 q = 1) (hb : d55878 q = 1) : d54822 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54362, d54822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1656 q ha hb
    | true =>
      simp only [d54362, d54822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54363 q = 1) (hb : d55878 q = 1) : d54823 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54363, d54823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54363, d54823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54364 q = 1) (hb : d55878 q = 1) : d54824 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54364, d54824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54364, d54824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54365 q = 1) (hb : d55878 q = 1) : d54825 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54365, d54825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54365, d54825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54366 q = 1) (hb : d55878 q = 1) : d54826 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54366, d54826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54366, d54826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54367 q = 1) (hb : d55878 q = 1) : d54827 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54367, d54827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54367, d54827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1658 (p : Pattern) (ha : d54373 p = 1) (hb : d55878 p = 1) : d54833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54368 q = 1) (hb : d55878 q = 1) : d54828 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54368, d54828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1657 q ha hb
    | true =>
      simp only [d54368, d54828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54369 q = 1) (hb : d55878 q = 1) : d54829 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54369, d54829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54369, d54829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54370 q = 1) (hb : d55878 q = 1) : d54830 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54370, d54830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54370, d54830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54371 q = 1) (hb : d55878 q = 1) : d54831 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54371, d54831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54371, d54831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54372 q = 1) (hb : d55878 q = 1) : d54832 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54372, d54832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54372, d54832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54373 q = 1) (hb : d55878 q = 1) : d54833 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54373, d54833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54373, d54833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1659 (p : Pattern) (ha : d54379 p = 1) (hb : d55878 p = 1) : d54839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54374 q = 1) (hb : d55878 q = 1) : d54834 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54374, d54834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1658 q ha hb
    | true =>
      simp only [d54374, d54834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54375 q = 1) (hb : d55878 q = 1) : d54835 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54375, d54835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54375, d54835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54376 q = 1) (hb : d55878 q = 1) : d54836 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54376, d54836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54376, d54836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54377 q = 1) (hb : d55878 q = 1) : d54837 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54377, d54837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54377, d54837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54378 q = 1) (hb : d55878 q = 1) : d54838 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54378, d54838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54378, d54838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54379 q = 1) (hb : d55878 q = 1) : d54839 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54379, d54839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54379, d54839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1660 (p : Pattern) (ha : d54385 p = 1) (hb : d55878 p = 1) : d54845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54380 q = 1) (hb : d55878 q = 1) : d54840 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54380, d54840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1659 q ha hb
    | true =>
      simp only [d54380, d54840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54381 q = 1) (hb : d55878 q = 1) : d54841 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54381, d54841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54381, d54841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54382 q = 1) (hb : d55878 q = 1) : d54842 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54382, d54842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54382, d54842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54383 q = 1) (hb : d55878 q = 1) : d54843 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54383, d54843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54383, d54843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54384 q = 1) (hb : d55878 q = 1) : d54844 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54384, d54844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54384, d54844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54385 q = 1) (hb : d55878 q = 1) : d54845 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54385, d54845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54385, d54845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1661 (p : Pattern) (ha : d54391 p = 1) (hb : d55878 p = 1) : d54851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54386 q = 1) (hb : d55878 q = 1) : d54846 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54386, d54846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1660 q ha hb
    | true =>
      simp only [d54386, d54846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54387 q = 1) (hb : d55878 q = 1) : d54847 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54387, d54847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54387, d54847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54388 q = 1) (hb : d55878 q = 1) : d54848 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54388, d54848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54388, d54848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54389 q = 1) (hb : d55878 q = 1) : d54849 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54389, d54849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54389, d54849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54390 q = 1) (hb : d55878 q = 1) : d54850 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54390, d54850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54390, d54850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54391 q = 1) (hb : d55878 q = 1) : d54851 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54391, d54851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54391, d54851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1662 (p : Pattern) (ha : d54397 p = 1) (hb : d55878 p = 1) : d54857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54392 q = 1) (hb : d55878 q = 1) : d54852 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54392, d54852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1661 q ha hb
    | true =>
      simp only [d54392, d54852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54393 q = 1) (hb : d55878 q = 1) : d54853 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54393, d54853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54393, d54853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54394 q = 1) (hb : d55878 q = 1) : d54854 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54394, d54854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54394, d54854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54395 q = 1) (hb : d55878 q = 1) : d54855 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54395, d54855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54395, d54855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54396 q = 1) (hb : d55878 q = 1) : d54856 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54396, d54856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54396, d54856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54397 q = 1) (hb : d55878 q = 1) : d54857 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54397, d54857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54397, d54857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1663 (p : Pattern) (ha : d54403 p = 1) (hb : d55878 p = 1) : d54863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54398 q = 1) (hb : d55878 q = 1) : d54858 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54398, d54858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1662 q ha hb
    | true =>
      simp only [d54398, d54858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54399 q = 1) (hb : d55878 q = 1) : d54859 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54399, d54859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54399, d54859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54400 q = 1) (hb : d55878 q = 1) : d54860 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54400, d54860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54400, d54860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54401 q = 1) (hb : d55878 q = 1) : d54861 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54401, d54861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54401, d54861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54402 q = 1) (hb : d55878 q = 1) : d54862 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54402, d54862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54402, d54862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54403 q = 1) (hb : d55878 q = 1) : d54863 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54403, d54863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54403, d54863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1664 (p : Pattern) (ha : d54404 p = 1) (hb : d55878 p = 1) : d54865 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53638 q = 1) : d53638 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53641 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53642 q = 1) (hb : d54517 q = 1) : d54864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d54517, d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53642, d54517, d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54404 q = 1) (hb : d55878 q = 1) : d54865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54404, d55878, d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54404, d55878, d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1665 (p : Pattern) (ha : d54410 p = 1) (hb : d55878 p = 1) : d54872 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53654 q = 1) : d53654 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53660 q = 1) (hb : d54517 q = 1) : d54871 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d54517, d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53660, d54517, d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54410 q = 1) (hb : d55878 q = 1) : d54872 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54410, d55878, d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54410, d55878, d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1666 (p : Pattern) (ha : d54416 p = 1) (hb : d55878 p = 1) : d54878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54405 q = 1) (hb : d55878 q = 1) : d54866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54405, d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54405, d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1664 q ha hb
  have h2 (q : Pattern) (ha : d54406 q = 1) (hb : d55878 q = 1) : d54867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54406, d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54406, d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54407 q = 1) (hb : d55878 q = 1) : d54868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54407, d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54407, d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54408 q = 1) (hb : d55878 q = 1) : d54869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54408, d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54408, d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54409 q = 1) (hb : d55878 q = 1) : d54870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54409, d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54409, d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54411 q = 1) (hb : d55878 q = 1) : d54873 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54411, d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54411, d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1665 q ha hb
  have h7 (q : Pattern) (ha : d54412 q = 1) (hb : d55878 q = 1) : d54874 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54412, d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54412, d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54413 q = 1) (hb : d55878 q = 1) : d54875 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54413, d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54413, d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54414 q = 1) (hb : d55878 q = 1) : d54876 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54414, d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54414, d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54415 q = 1) (hb : d55878 q = 1) : d54877 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54415, d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54415, d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54416 q = 1) (hb : d55878 q = 1) : d54878 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54416, d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54416, d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro1667 (p : Pattern) (ha : d54417 p = 1) (hb : d55878 p = 1) : d54880 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53679 q = 1) : d53679 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53685 q = 1) (hb : d54517 q = 1) : d54879 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d54517, d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53685, d54517, d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54417 q = 1) (hb : d55878 q = 1) : d54880 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54417, d55878, d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54417, d55878, d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1668 (p : Pattern) (ha : d54423 p = 1) (hb : d55878 p = 1) : d54886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54418 q = 1) (hb : d55878 q = 1) : d54881 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54418, d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54418, d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1667 q ha hb
  have h2 (q : Pattern) (ha : d54419 q = 1) (hb : d55878 q = 1) : d54882 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54419, d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54419, d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54420 q = 1) (hb : d55878 q = 1) : d54883 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54420, d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54420, d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54421 q = 1) (hb : d55878 q = 1) : d54884 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54421, d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54421, d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54422 q = 1) (hb : d55878 q = 1) : d54885 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54422, d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54422, d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54423 q = 1) (hb : d55878 q = 1) : d54886 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54423, d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54423, d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1669 (p : Pattern) (ha : d54425 p = 1) (hb : d55878 p = 1) : d54889 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53706 q = 1) : d53706 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53711 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53712 q = 1) (hb : d54517 q = 1) : d54888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d54517, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53712, d54517, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54425 q = 1) (hb : d55878 q = 1) : d54889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54425, d55878, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54425, d55878, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1670 (p : Pattern) (ha : d54431 p = 1) (hb : d55878 p = 1) : d54895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54426 q = 1) (hb : d55878 q = 1) : d54890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54426, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54426, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1669 q ha hb
  have h2 (q : Pattern) (ha : d54427 q = 1) (hb : d55878 q = 1) : d54891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54427, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54427, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54428 q = 1) (hb : d55878 q = 1) : d54892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54428, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54428, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54429 q = 1) (hb : d55878 q = 1) : d54893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54429, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54429, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54430 q = 1) (hb : d55878 q = 1) : d54894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54430, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54430, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54431 q = 1) (hb : d55878 q = 1) : d54895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54431, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54431, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1671 (p : Pattern) (ha : d54434 p = 1) (hb : d55878 p = 1) : d54899 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53734 q = 1) : d53734 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53740 q = 1) (hb : d54517 q = 1) : d54898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d54517, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53740, d54517, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54434 q = 1) (hb : d55878 q = 1) : d54899 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54434, d55878, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54434, d55878, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1672 (p : Pattern) (ha : d54440 p = 1) (hb : d55878 p = 1) : d54905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54435 q = 1) (hb : d55878 q = 1) : d54900 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54435, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54435, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1671 q ha hb
  have h2 (q : Pattern) (ha : d54436 q = 1) (hb : d55878 q = 1) : d54901 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54436, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54436, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54437 q = 1) (hb : d55878 q = 1) : d54902 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54437, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54437, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54438 q = 1) (hb : d55878 q = 1) : d54903 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54438, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54438, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54439 q = 1) (hb : d55878 q = 1) : d54904 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54439, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54439, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54440 q = 1) (hb : d55878 q = 1) : d54905 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54440, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54440, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1673 (p : Pattern) (ha : d54444 p = 1) (hb : d55878 p = 1) : d54910 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53763 q = 1) : d53763 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53768 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53769 q = 1) (hb : d54517 q = 1) : d54909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d54517, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53769, d54517, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54444 q = 1) (hb : d55878 q = 1) : d54910 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54444, d55878, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54444, d55878, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1674 (p : Pattern) (ha : d54450 p = 1) (hb : d55878 p = 1) : d54916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54445 q = 1) (hb : d55878 q = 1) : d54911 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54445, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54445, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1673 q ha hb
  have h2 (q : Pattern) (ha : d54446 q = 1) (hb : d55878 q = 1) : d54912 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54446, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54446, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54447 q = 1) (hb : d55878 q = 1) : d54913 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54447, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54447, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54448 q = 1) (hb : d55878 q = 1) : d54914 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54448, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54448, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54449 q = 1) (hb : d55878 q = 1) : d54915 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54449, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54449, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54450 q = 1) (hb : d55878 q = 1) : d54916 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54450, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54450, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1675 (p : Pattern) (ha : d54455 p = 1) (hb : d55878 p = 1) : d54922 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53793 q = 1) : d53793 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53798 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53799 q = 1) (hb : d54517 q = 1) : d54921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d54517, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53799, d54517, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54455 q = 1) (hb : d55878 q = 1) : d54922 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54455, d55878, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54455, d55878, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1676 (p : Pattern) (ha : d54461 p = 1) (hb : d55878 p = 1) : d54928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54456 q = 1) (hb : d55878 q = 1) : d54923 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54456, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54456, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1675 q ha hb
  have h2 (q : Pattern) (ha : d54457 q = 1) (hb : d55878 q = 1) : d54924 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54457, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54457, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54458 q = 1) (hb : d55878 q = 1) : d54925 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54458, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54458, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54459 q = 1) (hb : d55878 q = 1) : d54926 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54459, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54459, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54460 q = 1) (hb : d55878 q = 1) : d54927 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54460, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54460, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54461 q = 1) (hb : d55878 q = 1) : d54928 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54461, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54461, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1677 (p : Pattern) (ha : d54467 p = 1) (hb : d55878 p = 1) : d54934 p = 1 := by
  have h0 (q : Pattern) (ha : d54424 q = 1) (hb : d55878 q = 1) : d54887 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54424, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1666 q ha hb
    | true =>
      simp only [d54424, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1668 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54432 q = 1) (hb : d55878 q = 1) : d54896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54432, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54432, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1670 q ha hb
  have h3 (q : Pattern) (ha : d54433 q = 1) (hb : d55878 q = 1) : d54897 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54433, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54433, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54441 q = 1) (hb : d55878 q = 1) : d54906 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54441, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54441, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1672 q ha hb
  have h5 (q : Pattern) (ha : d54442 q = 1) (hb : d55878 q = 1) : d54907 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54442, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54442, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54443 q = 1) (hb : d55878 q = 1) : d54908 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54443, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54443, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54451 q = 1) (hb : d55878 q = 1) : d54917 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54451, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54451, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1674 q ha hb
  have h8 (q : Pattern) (ha : d54452 q = 1) (hb : d55878 q = 1) : d54918 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54452, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54452, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54453 q = 1) (hb : d55878 q = 1) : d54919 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54453, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54453, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54454 q = 1) (hb : d55878 q = 1) : d54920 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54454, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54454, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54462 q = 1) (hb : d55878 q = 1) : d54929 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54462, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54462, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1676 q ha hb
  have h12 (q : Pattern) (ha : d54463 q = 1) (hb : d55878 q = 1) : d54930 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54463, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54463, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54464 q = 1) (hb : d55878 q = 1) : d54931 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54464, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54464, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54465 q = 1) (hb : d55878 q = 1) : d54932 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54465, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54465, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54466 q = 1) (hb : d55878 q = 1) : d54933 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54466, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54466, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54467 q = 1) (hb : d55878 q = 1) : d54934 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54467, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54467, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1678 (p : Pattern) (ha : d54473 p = 1) (hb : d55878 p = 1) : d54940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54468 q = 1) (hb : d55878 q = 1) : d54935 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54468, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1677 q ha hb
    | true =>
      simp only [d54468, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54469 q = 1) (hb : d55878 q = 1) : d54936 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54469, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54469, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54470 q = 1) (hb : d55878 q = 1) : d54937 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54470, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54470, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54471 q = 1) (hb : d55878 q = 1) : d54938 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54471, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54471, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54472 q = 1) (hb : d55878 q = 1) : d54939 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54472, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54472, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54473 q = 1) (hb : d55878 q = 1) : d54940 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54473, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54473, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1679 (p : Pattern) (ha : d54479 p = 1) (hb : d55878 p = 1) : d54946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54474 q = 1) (hb : d55878 q = 1) : d54941 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54474, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1678 q ha hb
    | true =>
      simp only [d54474, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54475 q = 1) (hb : d55878 q = 1) : d54942 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54475, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54475, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54476 q = 1) (hb : d55878 q = 1) : d54943 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54476, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54476, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54477 q = 1) (hb : d55878 q = 1) : d54944 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54477, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54477, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54478 q = 1) (hb : d55878 q = 1) : d54945 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54478, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54478, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54479 q = 1) (hb : d55878 q = 1) : d54946 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54479, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54479, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1680 (p : Pattern) (ha : d54485 p = 1) (hb : d55878 p = 1) : d54952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54480 q = 1) (hb : d55878 q = 1) : d54947 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54480, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1679 q ha hb
    | true =>
      simp only [d54480, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54481 q = 1) (hb : d55878 q = 1) : d54948 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54481, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54481, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54482 q = 1) (hb : d55878 q = 1) : d54949 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54482, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54482, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54483 q = 1) (hb : d55878 q = 1) : d54950 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54483, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54483, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54484 q = 1) (hb : d55878 q = 1) : d54951 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54484, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54484, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54485 q = 1) (hb : d55878 q = 1) : d54952 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54485, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54485, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1681 (p : Pattern) (ha : d54491 p = 1) (hb : d55878 p = 1) : d54958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54486 q = 1) (hb : d55878 q = 1) : d54953 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54486, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1680 q ha hb
    | true =>
      simp only [d54486, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54487 q = 1) (hb : d55878 q = 1) : d54954 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54487, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54487, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54488 q = 1) (hb : d55878 q = 1) : d54955 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54488, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54488, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54489 q = 1) (hb : d55878 q = 1) : d54956 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54489, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54489, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54490 q = 1) (hb : d55878 q = 1) : d54957 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54490, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54490, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54491 q = 1) (hb : d55878 q = 1) : d54958 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54491, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54491, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1682 (p : Pattern) (ha : d54497 p = 1) (hb : d55878 p = 1) : d54964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54492 q = 1) (hb : d55878 q = 1) : d54959 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54492, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1681 q ha hb
    | true =>
      simp only [d54492, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54493 q = 1) (hb : d55878 q = 1) : d54960 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54493, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54493, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54494 q = 1) (hb : d55878 q = 1) : d54961 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54494, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54494, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54495 q = 1) (hb : d55878 q = 1) : d54962 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54495, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54495, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54496 q = 1) (hb : d55878 q = 1) : d54963 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54496, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54496, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54497 q = 1) (hb : d55878 q = 1) : d54964 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54497, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54497, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1683 (p : Pattern) (ha : d54503 p = 1) (hb : d55878 p = 1) : d54970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54498 q = 1) (hb : d55878 q = 1) : d54965 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54498, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1682 q ha hb
    | true =>
      simp only [d54498, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54499 q = 1) (hb : d55878 q = 1) : d54966 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54499, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54499, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54500 q = 1) (hb : d55878 q = 1) : d54967 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54500, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54500, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54501 q = 1) (hb : d55878 q = 1) : d54968 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54501, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54501, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54502 q = 1) (hb : d55878 q = 1) : d54969 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54502, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54502, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54503 q = 1) (hb : d55878 q = 1) : d54970 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54503, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54503, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1684 (p : Pattern) (ha : d54509 p = 1) (hb : d55878 p = 1) : d54976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54504 q = 1) (hb : d55878 q = 1) : d54971 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54504, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1683 q ha hb
    | true =>
      simp only [d54504, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54505 q = 1) (hb : d55878 q = 1) : d54972 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54505, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54505, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54506 q = 1) (hb : d55878 q = 1) : d54973 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54506, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54506, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54507 q = 1) (hb : d55878 q = 1) : d54974 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54507, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54507, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54508 q = 1) (hb : d55878 q = 1) : d54975 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54508, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54508, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54509 q = 1) (hb : d55878 q = 1) : d54976 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54509, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54509, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1685 (p : Pattern) (ha : d2672 p = 1) (hb : d61810 p = 1) : d62034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d64 q = 1) (hb : d55754 q = 1) : d64 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d65 q = 1) (hb : d61809 q = 1) : d62033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, d61809, d62033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d65, d61809, d62033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2672 q = 1) (hb : d61810 q = 1) : d62034 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2672, d61810, d62034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2672, d61810, d62034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1686 (p : Pattern) (ha : d54298 p = 1) (hb : d61810 p = 1) : d62040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4353 q = 1) (hb : d55754 q = 1) : d4353 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51651 q = 1) (hb : d61809 q = 1) : d62039 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d61809, d62039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51651, d61809, d62039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54298 q = 1) (hb : d61810 q = 1) : d62040 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54298, d61810, d62040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54298, d61810, d62040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1687 (p : Pattern) (ha : d54304 p = 1) (hb : d61810 p = 1) : d62047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51667 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51670 q = 1) (hb : d55754 q = 1) : d51670 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51671 q = 1) (hb : d61809 q = 1) : d62046 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d61809, d62046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51671, d61809, d62046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54304 q = 1) (hb : d61810 q = 1) : d62047 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54304, d61810, d62047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54304, d61810, d62047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1688 (p : Pattern) (ha : d54310 p = 1) (hb : d61810 p = 1) : d62053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2673 q = 1) (hb : d61810 q = 1) : d62035 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2673, d62035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2673, d62035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1685 q ha hb
  have h2 (q : Pattern) (ha : d2674 q = 1) (hb : d61810 q = 1) : d62036 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2674, d62036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2674, d62036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2675 q = 1) (hb : d61810 q = 1) : d62037 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2675, d62037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2675, d62037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2676 q = 1) (hb : d61810 q = 1) : d62038 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2676, d62038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2676, d62038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54299 q = 1) (hb : d61810 q = 1) : d62041 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54299, d62041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54299, d62041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1686 q ha hb
  have h6 (q : Pattern) (ha : d54300 q = 1) (hb : d61810 q = 1) : d62042 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54300, d62042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54300, d62042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54301 q = 1) (hb : d61810 q = 1) : d62043 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54301, d62043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54301, d62043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54302 q = 1) (hb : d61810 q = 1) : d62044 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54302, d62044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54302, d62044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54303 q = 1) (hb : d61810 q = 1) : d62045 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54303, d62045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54303, d62045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54305 q = 1) (hb : d61810 q = 1) : d62048 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54305, d62048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54305, d62048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1687 q ha hb
  have h11 (q : Pattern) (ha : d54306 q = 1) (hb : d61810 q = 1) : d62049 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54306, d62049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54306, d62049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54307 q = 1) (hb : d61810 q = 1) : d62050 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54307, d62050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54307, d62050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54308 q = 1) (hb : d61810 q = 1) : d62051 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54308, d62051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54308, d62051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54309 q = 1) (hb : d61810 q = 1) : d62052 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54309, d62052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54309, d62052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54310 q = 1) (hb : d61810 q = 1) : d62053 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54310, d62053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54310, d62053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1689 (p : Pattern) (ha : d54311 p = 1) (hb : d61810 p = 1) : d62055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51692 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51695 q = 1) (hb : d55754 q = 1) : d51695 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51696 q = 1) (hb : d61809 q = 1) : d62054 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d61809, d62054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51696, d61809, d62054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54311 q = 1) (hb : d61810 q = 1) : d62055 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54311, d61810, d62055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54311, d61810, d62055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1690 (p : Pattern) (ha : d54317 p = 1) (hb : d61810 p = 1) : d62061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54312 q = 1) (hb : d61810 q = 1) : d62056 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54312, d62056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54312, d62056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1689 q ha hb
  have h2 (q : Pattern) (ha : d54313 q = 1) (hb : d61810 q = 1) : d62057 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54313, d62057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54313, d62057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54314 q = 1) (hb : d61810 q = 1) : d62058 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54314, d62058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54314, d62058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54315 q = 1) (hb : d61810 q = 1) : d62059 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54315, d62059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54315, d62059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54316 q = 1) (hb : d61810 q = 1) : d62060 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54316, d62060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54316, d62060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54317 q = 1) (hb : d61810 q = 1) : d62061 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54317, d62061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54317, d62061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1691 (p : Pattern) (ha : d54319 p = 1) (hb : d61810 p = 1) : d62064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51721 q = 1) (hb : d55754 q = 1) : d51721 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51722 q = 1) (hb : d61809 q = 1) : d62063 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d61809, d62063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51722, d61809, d62063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54319 q = 1) (hb : d61810 q = 1) : d62064 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54319, d61810, d62064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54319, d61810, d62064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1692 (p : Pattern) (ha : d54325 p = 1) (hb : d61810 p = 1) : d62070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54320 q = 1) (hb : d61810 q = 1) : d62065 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54320, d62065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54320, d62065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1691 q ha hb
  have h2 (q : Pattern) (ha : d54321 q = 1) (hb : d61810 q = 1) : d62066 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54321, d62066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54321, d62066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54322 q = 1) (hb : d61810 q = 1) : d62067 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54322, d62067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54322, d62067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54323 q = 1) (hb : d61810 q = 1) : d62068 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54323, d62068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54323, d62068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54324 q = 1) (hb : d61810 q = 1) : d62069 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54324, d62069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54324, d62069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54325 q = 1) (hb : d61810 q = 1) : d62070 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54325, d62070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54325, d62070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1693 (p : Pattern) (ha : d54328 p = 1) (hb : d61810 p = 1) : d62074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51745 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51748 q = 1) (hb : d55754 q = 1) : d51748 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51749 q = 1) (hb : d61809 q = 1) : d62073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d61809, d62073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51749, d61809, d62073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54328 q = 1) (hb : d61810 q = 1) : d62074 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54328, d61810, d62074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54328, d61810, d62074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1694 (p : Pattern) (ha : d54334 p = 1) (hb : d61810 p = 1) : d62080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54329 q = 1) (hb : d61810 q = 1) : d62075 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54329, d62075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54329, d62075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1693 q ha hb
  have h2 (q : Pattern) (ha : d54330 q = 1) (hb : d61810 q = 1) : d62076 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54330, d62076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54330, d62076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54331 q = 1) (hb : d61810 q = 1) : d62077 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54331, d62077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54331, d62077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54332 q = 1) (hb : d61810 q = 1) : d62078 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54332, d62078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54332, d62078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54333 q = 1) (hb : d61810 q = 1) : d62079 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54333, d62079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54333, d62079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54334 q = 1) (hb : d61810 q = 1) : d62080 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54334, d62080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54334, d62080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1695 (p : Pattern) (ha : d54338 p = 1) (hb : d61810 p = 1) : d62085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51776 q = 1) (hb : d55754 q = 1) : d51776 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51777 q = 1) (hb : d61809 q = 1) : d62084 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d61809, d62084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51777, d61809, d62084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54338 q = 1) (hb : d61810 q = 1) : d62085 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54338, d61810, d62085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54338, d61810, d62085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1696 (p : Pattern) (ha : d54344 p = 1) (hb : d61810 p = 1) : d62091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54339 q = 1) (hb : d61810 q = 1) : d62086 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54339, d62086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54339, d62086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1695 q ha hb
  have h2 (q : Pattern) (ha : d54340 q = 1) (hb : d61810 q = 1) : d62087 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54340, d62087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54340, d62087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54341 q = 1) (hb : d61810 q = 1) : d62088 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54341, d62088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54341, d62088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54342 q = 1) (hb : d61810 q = 1) : d62089 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54342, d62089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54342, d62089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54343 q = 1) (hb : d61810 q = 1) : d62090 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54343, d62090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54343, d62090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54344 q = 1) (hb : d61810 q = 1) : d62091 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54344, d62091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54344, d62091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1697 (p : Pattern) (ha : d54349 p = 1) (hb : d61810 p = 1) : d62097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51805 q = 1) (hb : d55754 q = 1) : d51805 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51806 q = 1) (hb : d61809 q = 1) : d62096 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d61809, d62096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51806, d61809, d62096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54349 q = 1) (hb : d61810 q = 1) : d62097 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54349, d61810, d62097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54349, d61810, d62097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1698 (p : Pattern) (ha : d54355 p = 1) (hb : d61810 p = 1) : d62103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54350 q = 1) (hb : d61810 q = 1) : d62098 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54350, d62098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54350, d62098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1697 q ha hb
  have h2 (q : Pattern) (ha : d54351 q = 1) (hb : d61810 q = 1) : d62099 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54351, d62099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54351, d62099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54352 q = 1) (hb : d61810 q = 1) : d62100 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54352, d62100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54352, d62100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54353 q = 1) (hb : d61810 q = 1) : d62101 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54353, d62101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54353, d62101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54354 q = 1) (hb : d61810 q = 1) : d62102 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54354, d62102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54354, d62102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54355 q = 1) (hb : d61810 q = 1) : d62103 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54355, d62103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54355, d62103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1699 (p : Pattern) (ha : d54361 p = 1) (hb : d61810 p = 1) : d62109 p = 1 := by
  have h0 (q : Pattern) (ha : d54318 q = 1) (hb : d61810 q = 1) : d62062 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54318, d62062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1688 q ha hb
    | true =>
      simp only [d54318, d62062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1690 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54326 q = 1) (hb : d61810 q = 1) : d62071 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54326, d62071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54326, d62071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1692 q ha hb
  have h3 (q : Pattern) (ha : d54327 q = 1) (hb : d61810 q = 1) : d62072 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54327, d62072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54327, d62072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54335 q = 1) (hb : d61810 q = 1) : d62081 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54335, d62081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54335, d62081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1694 q ha hb
  have h5 (q : Pattern) (ha : d54336 q = 1) (hb : d61810 q = 1) : d62082 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54336, d62082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54336, d62082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54337 q = 1) (hb : d61810 q = 1) : d62083 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54337, d62083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54337, d62083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54345 q = 1) (hb : d61810 q = 1) : d62092 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54345, d62092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54345, d62092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1696 q ha hb
  have h8 (q : Pattern) (ha : d54346 q = 1) (hb : d61810 q = 1) : d62093 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54346, d62093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54346, d62093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54347 q = 1) (hb : d61810 q = 1) : d62094 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54347, d62094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54347, d62094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54348 q = 1) (hb : d61810 q = 1) : d62095 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54348, d62095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54348, d62095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54356 q = 1) (hb : d61810 q = 1) : d62104 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54356, d62104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54356, d62104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1698 q ha hb
  have h12 (q : Pattern) (ha : d54357 q = 1) (hb : d61810 q = 1) : d62105 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54357, d62105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54357, d62105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54358 q = 1) (hb : d61810 q = 1) : d62106 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54358, d62106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54358, d62106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54359 q = 1) (hb : d61810 q = 1) : d62107 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54359, d62107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54359, d62107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54360 q = 1) (hb : d61810 q = 1) : d62108 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54360, d62108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54360, d62108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54361 q = 1) (hb : d61810 q = 1) : d62109 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54361, d62109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54361, d62109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1700 (p : Pattern) (ha : d54367 p = 1) (hb : d61810 p = 1) : d62115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54362 q = 1) (hb : d61810 q = 1) : d62110 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54362, d62110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1699 q ha hb
    | true =>
      simp only [d54362, d62110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54363 q = 1) (hb : d61810 q = 1) : d62111 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54363, d62111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54363, d62111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54364 q = 1) (hb : d61810 q = 1) : d62112 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54364, d62112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54364, d62112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54365 q = 1) (hb : d61810 q = 1) : d62113 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54365, d62113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54365, d62113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54366 q = 1) (hb : d61810 q = 1) : d62114 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54366, d62114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54366, d62114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54367 q = 1) (hb : d61810 q = 1) : d62115 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54367, d62115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54367, d62115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1701 (p : Pattern) (ha : d54373 p = 1) (hb : d61810 p = 1) : d62121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54368 q = 1) (hb : d61810 q = 1) : d62116 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54368, d62116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1700 q ha hb
    | true =>
      simp only [d54368, d62116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54369 q = 1) (hb : d61810 q = 1) : d62117 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54369, d62117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54369, d62117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54370 q = 1) (hb : d61810 q = 1) : d62118 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54370, d62118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54370, d62118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54371 q = 1) (hb : d61810 q = 1) : d62119 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54371, d62119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54371, d62119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54372 q = 1) (hb : d61810 q = 1) : d62120 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54372, d62120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54372, d62120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54373 q = 1) (hb : d61810 q = 1) : d62121 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54373, d62121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54373, d62121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1702 (p : Pattern) (ha : d54379 p = 1) (hb : d61810 p = 1) : d62127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54374 q = 1) (hb : d61810 q = 1) : d62122 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54374, d62122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1701 q ha hb
    | true =>
      simp only [d54374, d62122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54375 q = 1) (hb : d61810 q = 1) : d62123 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54375, d62123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54375, d62123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54376 q = 1) (hb : d61810 q = 1) : d62124 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54376, d62124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54376, d62124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54377 q = 1) (hb : d61810 q = 1) : d62125 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54377, d62125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54377, d62125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54378 q = 1) (hb : d61810 q = 1) : d62126 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54378, d62126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54378, d62126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54379 q = 1) (hb : d61810 q = 1) : d62127 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54379, d62127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54379, d62127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1703 (p : Pattern) (ha : d54385 p = 1) (hb : d61810 p = 1) : d62133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54380 q = 1) (hb : d61810 q = 1) : d62128 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54380, d62128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1702 q ha hb
    | true =>
      simp only [d54380, d62128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54381 q = 1) (hb : d61810 q = 1) : d62129 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54381, d62129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54381, d62129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54382 q = 1) (hb : d61810 q = 1) : d62130 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54382, d62130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54382, d62130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54383 q = 1) (hb : d61810 q = 1) : d62131 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54383, d62131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54383, d62131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54384 q = 1) (hb : d61810 q = 1) : d62132 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54384, d62132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54384, d62132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54385 q = 1) (hb : d61810 q = 1) : d62133 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54385, d62133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54385, d62133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1704 (p : Pattern) (ha : d54391 p = 1) (hb : d61810 p = 1) : d62139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54386 q = 1) (hb : d61810 q = 1) : d62134 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54386, d62134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1703 q ha hb
    | true =>
      simp only [d54386, d62134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54387 q = 1) (hb : d61810 q = 1) : d62135 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54387, d62135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54387, d62135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54388 q = 1) (hb : d61810 q = 1) : d62136 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54388, d62136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54388, d62136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54389 q = 1) (hb : d61810 q = 1) : d62137 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54389, d62137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54389, d62137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54390 q = 1) (hb : d61810 q = 1) : d62138 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54390, d62138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54390, d62138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54391 q = 1) (hb : d61810 q = 1) : d62139 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54391, d62139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54391, d62139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1705 (p : Pattern) (ha : d54397 p = 1) (hb : d61810 p = 1) : d62145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54392 q = 1) (hb : d61810 q = 1) : d62140 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54392, d62140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1704 q ha hb
    | true =>
      simp only [d54392, d62140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54393 q = 1) (hb : d61810 q = 1) : d62141 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54393, d62141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54393, d62141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54394 q = 1) (hb : d61810 q = 1) : d62142 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54394, d62142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54394, d62142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54395 q = 1) (hb : d61810 q = 1) : d62143 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54395, d62143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54395, d62143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54396 q = 1) (hb : d61810 q = 1) : d62144 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54396, d62144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54396, d62144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54397 q = 1) (hb : d61810 q = 1) : d62145 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54397, d62145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54397, d62145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1706 (p : Pattern) (ha : d54403 p = 1) (hb : d61810 p = 1) : d62151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54398 q = 1) (hb : d61810 q = 1) : d62146 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54398, d62146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1705 q ha hb
    | true =>
      simp only [d54398, d62146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54399 q = 1) (hb : d61810 q = 1) : d62147 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54399, d62147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54399, d62147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54400 q = 1) (hb : d61810 q = 1) : d62148 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54400, d62148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54400, d62148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54401 q = 1) (hb : d61810 q = 1) : d62149 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54401, d62149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54401, d62149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54402 q = 1) (hb : d61810 q = 1) : d62150 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54402, d62150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54402, d62150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54403 q = 1) (hb : d61810 q = 1) : d62151 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54403, d62151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54403, d62151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1707 (p : Pattern) (ha : d60 p = 1) (hb : d51907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d52 q = 1) (hb : d51904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d51904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52, d51904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d53 q = 1) (hb : d51905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, d51905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53, d51905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54 q = 1) (hb : d51906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, d51906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54, d51906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60 q = 1) (hb : d51907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, d51907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, d51907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1708 (p : Pattern) (ha : d61922 p = 1) (hb : d62034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1707 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d64 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51910 q = 1) (hb : d62033 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61922 q = 1) (hb : d62034 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61922, d62034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61922, d62034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h8 p ha hb
theorem andIntro1709 (p : Pattern) (ha : d4349 p = 1) (hb : d52029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4340 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4340, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4341 q = 1) (hb : d52026 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d52026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4341, d52026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4342 q = 1) (hb : d52027 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d52027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4342, d52027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4343 q = 1) (hb : d52028 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d52028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4343, d52028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4349 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d52029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d52029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1710 (p : Pattern) (ha : d61927 p = 1) (hb : d62040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4350 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4350, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1709 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4351 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4351, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4352 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4352, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4353 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52034 q = 1) (hb : d62039 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d61927 q = 1) (hb : d62040 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61927, d62040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61927, d62040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro1711 (p : Pattern) (ha : d406 p = 1) (hb : d51963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d51959 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d51959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d51959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d51960 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d51960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d51960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d51961 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d51961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109, d51961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d51962 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d51962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d110, d51962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d51963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d51963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1712 (p : Pattern) (ha : d4385 p = 1) (hb : d52161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4376 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d391 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4377 q = 1) (hb : d52158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d52158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4377, d52158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4378 q = 1) (hb : d52159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d52159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4378, d52159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4379 q = 1) (hb : d52160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d52160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4379, d52160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4385 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d52161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d52161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1713 (p : Pattern) (ha : d61933 p = 1) (hb : d62047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4386 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4386, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1712 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d407 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d407, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1711 q ha hb
  have h5 (q : Pattern) (ha : d51668 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51668, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51669 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51669, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51670 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52166 q = 1) (hb : d62046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d61933 q = 1) (hb : d62047 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61933, d62047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61933, d62047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h10 p ha hb
theorem andIntro1714 (p : Pattern) (ha : d61939 p = 1) (hb : d62053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61923 q = 1) (hb : d62035 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61923, d62035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61923, d62035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1708 q ha hb
  have h2 (q : Pattern) (ha : d61924 q = 1) (hb : d62036 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61924, d62036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61924, d62036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61925 q = 1) (hb : d62037 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61925, d62037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61925, d62037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61926 q = 1) (hb : d62038 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61926, d62038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61926, d62038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61928 q = 1) (hb : d62041 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61928, d62041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61928, d62041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1710 q ha hb
  have h6 (q : Pattern) (ha : d61929 q = 1) (hb : d62042 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61929, d62042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61929, d62042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61930 q = 1) (hb : d62043 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61930, d62043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61930, d62043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61931 q = 1) (hb : d62044 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61931, d62044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61931, d62044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61932 q = 1) (hb : d62045 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61932, d62045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61932, d62045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61934 q = 1) (hb : d62048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61934, d62048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61934, d62048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1713 q ha hb
  have h11 (q : Pattern) (ha : d61935 q = 1) (hb : d62049 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61935, d62049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61935, d62049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61936 q = 1) (hb : d62050 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61936, d62050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61936, d62050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61937 q = 1) (hb : d62051 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61937, d62051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61937, d62051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61938 q = 1) (hb : d62052 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61938, d62052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61938, d62052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61939 q = 1) (hb : d62053 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61939, d62053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61939, d62053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1715 (p : Pattern) (ha : d653 p = 1) (hb : d52348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d639 q = 1) (hb : d52343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
    | true =>
      simp only [d639, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d640 q = 1) (hb : d52344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d641 q = 1) (hb : d52345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d641, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d642 q = 1) (hb : d52346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d642, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d643 q = 1) (hb : d52347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d643, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d653 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1716 (p : Pattern) (ha : d4422 p = 1) (hb : d52335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d621 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4413 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4413, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d626 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d627 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4414 q = 1) (hb : d52332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d52332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4414, d52332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4415 q = 1) (hb : d52333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d52333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4415, d52333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4416 q = 1) (hb : d52334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d52334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4416, d52334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4422 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d52335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d52335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1717 (p : Pattern) (ha : d61940 p = 1) (hb : d62055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4423 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4423, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1716 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d654 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d654, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1715 q ha hb
  have h5 (q : Pattern) (ha : d51693 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51693, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51694 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51694, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51695 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52351 q = 1) (hb : d62054 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d61940 q = 1) (hb : d62055 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61940, d62055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61940, d62055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h10 p ha hb
theorem andIntro1718 (p : Pattern) (ha : d61946 p = 1) (hb : d62061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61941 q = 1) (hb : d62056 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61941, d62056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61941, d62056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1717 q ha hb
  have h2 (q : Pattern) (ha : d61942 q = 1) (hb : d62057 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61942, d62057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61942, d62057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61943 q = 1) (hb : d62058 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61943, d62058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61943, d62058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61944 q = 1) (hb : d62059 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61944, d62059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61944, d62059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61945 q = 1) (hb : d62060 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61945, d62060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61945, d62060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61946 q = 1) (hb : d62061 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61946, d62061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61946, d62061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1719 (p : Pattern) (ha : d959 p = 1) (hb : d52569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d945 q = 1) (hb : d52564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
    | true =>
      simp only [d945, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d946 q = 1) (hb : d52565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d947 q = 1) (hb : d52566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d947, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d948 q = 1) (hb : d52567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d948, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d949 q = 1) (hb : d52568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d949, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d959 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1720 (p : Pattern) (ha : d4460 p = 1) (hb : d52556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d927 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4451 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4451, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d932 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d933 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4452 q = 1) (hb : d52553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d52553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4452, d52553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4453 q = 1) (hb : d52554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d52554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4453, d52554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4454 q = 1) (hb : d52555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d52555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4454, d52555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4460 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d52556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d52556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1721 (p : Pattern) (ha : d61948 p = 1) (hb : d62064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4461 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4461, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1720 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d960 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d960, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1719 q ha hb
  have h5 (q : Pattern) (ha : d51719 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51719, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51720 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51720, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51721 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52572 q = 1) (hb : d62063 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d61948 q = 1) (hb : d62064 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61948, d62064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61948, d62064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h10 p ha hb
theorem andIntro1722 (p : Pattern) (ha : d61954 p = 1) (hb : d62070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61949 q = 1) (hb : d62065 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61949, d62065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61949, d62065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1721 q ha hb
  have h2 (q : Pattern) (ha : d61950 q = 1) (hb : d62066 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61950, d62066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61950, d62066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61951 q = 1) (hb : d62067 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61951, d62067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61951, d62067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61952 q = 1) (hb : d62068 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61952, d62068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61952, d62068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61953 q = 1) (hb : d62069 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61953, d62069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61953, d62069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61954 q = 1) (hb : d62070 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61954, d62070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61954, d62070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1723 (p : Pattern) (ha : d1370 p = 1) (hb : d52849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1356 q = 1) (hb : d52844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d52844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
    | true =>
      simp only [d1356, d52844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1357 q = 1) (hb : d52845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d52845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d52845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1358 q = 1) (hb : d52846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d52846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1358, d52846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1359 q = 1) (hb : d52847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d52847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1359, d52847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1360 q = 1) (hb : d52848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d52848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1360, d52848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1370 q = 1) (hb : d52849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d52849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d52849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1724 (p : Pattern) (ha : d4499 p = 1) (hb : d52836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4490 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1343 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1344 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4491 q = 1) (hb : d52833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d52833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4491, d52833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4492 q = 1) (hb : d52834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d52834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4492, d52834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4493 q = 1) (hb : d52835 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d52835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4493, d52835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4499 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d52836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d52836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1725 (p : Pattern) (ha : d61957 p = 1) (hb : d62074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4500 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4500, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1724 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1371 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1371, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1723 q ha hb
  have h5 (q : Pattern) (ha : d51746 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51746, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51747 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51747, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51748 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52852 q = 1) (hb : d62073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d61957 q = 1) (hb : d62074 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61957, d62074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61957, d62074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h10 p ha hb
theorem andIntro1726 (p : Pattern) (ha : d61963 p = 1) (hb : d62080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61958 q = 1) (hb : d62075 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61958, d62075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61958, d62075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1725 q ha hb
  have h2 (q : Pattern) (ha : d61959 q = 1) (hb : d62076 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61959, d62076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61959, d62076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61960 q = 1) (hb : d62077 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61960, d62077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61960, d62077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61961 q = 1) (hb : d62078 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61961, d62078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61961, d62078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61962 q = 1) (hb : d62079 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61962, d62079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61962, d62079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61963 q = 1) (hb : d62080 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61963, d62080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61963, d62080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1727 (p : Pattern) (ha : d1847 p = 1) (hb : d53164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1833 q = 1) (hb : d53159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d53159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
    | true =>
      simp only [d1833, d53159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1834 q = 1) (hb : d53160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d53160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d53160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1835 q = 1) (hb : d53161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d53161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1835, d53161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1836 q = 1) (hb : d53162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d53162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1836, d53162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1837 q = 1) (hb : d53163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d53163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1837, d53163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1847 q = 1) (hb : d53164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d53164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d53164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1728 (p : Pattern) (ha : d4539 p = 1) (hb : d53151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4530 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1820 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1821 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4531 q = 1) (hb : d53148 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d53148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4531, d53148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4532 q = 1) (hb : d53149 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d53149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4532, d53149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4533 q = 1) (hb : d53150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d53150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4533, d53150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4539 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d53151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d53151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1729 (p : Pattern) (ha : d61967 p = 1) (hb : d62085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4540 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4540, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1728 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1848 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1848, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1727 q ha hb
  have h5 (q : Pattern) (ha : d51774 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51774, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51775 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51775, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51776 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53167 q = 1) (hb : d62084 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d61967 q = 1) (hb : d62085 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61967, d62085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61967, d62085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h10 p ha hb
theorem andIntro1730 (p : Pattern) (ha : d61973 p = 1) (hb : d62091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61968 q = 1) (hb : d62086 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61968, d62086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61968, d62086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1729 q ha hb
  have h2 (q : Pattern) (ha : d61969 q = 1) (hb : d62087 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61969, d62087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61969, d62087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61970 q = 1) (hb : d62088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61970, d62088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61970, d62088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61971 q = 1) (hb : d62089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61971, d62089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61971, d62089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61972 q = 1) (hb : d62090 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61972, d62090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61972, d62090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61973 q = 1) (hb : d62091 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61973, d62091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61973, d62091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1731 (p : Pattern) (ha : d2325 p = 1) (hb : d53481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2311 q = 1) (hb : d53476 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d53476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
    | true =>
      simp only [d2311, d53476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2312 q = 1) (hb : d53477 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d53477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d53477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2313 q = 1) (hb : d53478 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d53478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2313, d53478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2314 q = 1) (hb : d53479 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d53479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2314, d53479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2315 q = 1) (hb : d53480 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d53480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2315, d53480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2325 q = 1) (hb : d53481 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d53481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d53481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1732 (p : Pattern) (ha : d4580 p = 1) (hb : d53468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4571 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2298 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2299 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d4572 q = 1) (hb : d53465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d53465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4572, d53465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4573 q = 1) (hb : d53466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d53466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4573, d53466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4574 q = 1) (hb : d53467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d53467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4574, d53467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4580 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d53468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d53468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1733 (p : Pattern) (ha : d61978 p = 1) (hb : d62097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4581 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4581, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1732 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2326 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2326, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1731 q ha hb
  have h5 (q : Pattern) (ha : d51803 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51803, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51804 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51804, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51805 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53484 q = 1) (hb : d62096 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d61978 q = 1) (hb : d62097 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61978, d62097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61978, d62097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h10 p ha hb
theorem andIntro1734 (p : Pattern) (ha : d61984 p = 1) (hb : d62103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61979 q = 1) (hb : d62098 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61979, d62098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61979, d62098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1733 q ha hb
  have h2 (q : Pattern) (ha : d61980 q = 1) (hb : d62099 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61980, d62099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61980, d62099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61981 q = 1) (hb : d62100 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61981, d62100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61981, d62100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61982 q = 1) (hb : d62101 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61982, d62101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61982, d62101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61983 q = 1) (hb : d62102 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61983, d62102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61983, d62102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61984 q = 1) (hb : d62103 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61984, d62103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61984, d62103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1735 (p : Pattern) (ha : d61990 p = 1) (hb : d62109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61947 q = 1) (hb : d62062 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61947, d62062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1714 q ha hb
    | true =>
      simp only [d61947, d62062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1718 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61955 q = 1) (hb : d62071 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61955, d62071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61955, d62071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1722 q ha hb
  have h3 (q : Pattern) (ha : d61956 q = 1) (hb : d62072 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61956, d62072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61956, d62072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61964 q = 1) (hb : d62081 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61964, d62081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61964, d62081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1726 q ha hb
  have h5 (q : Pattern) (ha : d61965 q = 1) (hb : d62082 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61965, d62082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61965, d62082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61966 q = 1) (hb : d62083 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61966, d62083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61966, d62083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61974 q = 1) (hb : d62092 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61974, d62092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61974, d62092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1730 q ha hb
  have h8 (q : Pattern) (ha : d61975 q = 1) (hb : d62093 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61975, d62093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61975, d62093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61976 q = 1) (hb : d62094 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61976, d62094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61976, d62094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61977 q = 1) (hb : d62095 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61977, d62095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61977, d62095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61985 q = 1) (hb : d62104 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61985, d62104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61985, d62104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1734 q ha hb
  have h12 (q : Pattern) (ha : d61986 q = 1) (hb : d62105 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61986, d62105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61986, d62105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61987 q = 1) (hb : d62106 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61987, d62106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61987, d62106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61988 q = 1) (hb : d62107 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61988, d62107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61988, d62107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61989 q = 1) (hb : d62108 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61989, d62108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61989, d62108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61990 q = 1) (hb : d62109 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61990, d62109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61990, d62109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro1736 (p : Pattern) (ha : d61996 p = 1) (hb : d62115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61991 q = 1) (hb : d62110 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61991, d62110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1735 q ha hb
    | true =>
      simp only [d61991, d62110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61992 q = 1) (hb : d62111 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61992, d62111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61992, d62111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61993 q = 1) (hb : d62112 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61993, d62112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61993, d62112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61994 q = 1) (hb : d62113 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61994, d62113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61994, d62113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61995 q = 1) (hb : d62114 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61995, d62114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61995, d62114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61996 q = 1) (hb : d62115 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61996, d62115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61996, d62115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1737 (p : Pattern) (ha : d62002 p = 1) (hb : d62121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61997 q = 1) (hb : d62116 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61997, d62116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1736 q ha hb
    | true =>
      simp only [d61997, d62116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61998 q = 1) (hb : d62117 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61998, d62117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61998, d62117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61999 q = 1) (hb : d62118 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61999, d62118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61999, d62118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62000 q = 1) (hb : d62119 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62000, d62119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62000, d62119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62001 q = 1) (hb : d62120 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62001, d62120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62001, d62120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62002 q = 1) (hb : d62121 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62002, d62121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62002, d62121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1738 (p : Pattern) (ha : d62008 p = 1) (hb : d62127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62003 q = 1) (hb : d62122 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62003, d62122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1737 q ha hb
    | true =>
      simp only [d62003, d62122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62004 q = 1) (hb : d62123 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62004, d62123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62004, d62123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62005 q = 1) (hb : d62124 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62005, d62124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62005, d62124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62006 q = 1) (hb : d62125 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62006, d62125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62006, d62125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62007 q = 1) (hb : d62126 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62007, d62126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62007, d62126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62008 q = 1) (hb : d62127 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62008, d62127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62008, d62127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1739 (p : Pattern) (ha : d62014 p = 1) (hb : d62133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62009 q = 1) (hb : d62128 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62009, d62128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1738 q ha hb
    | true =>
      simp only [d62009, d62128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62010 q = 1) (hb : d62129 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62010, d62129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62010, d62129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62011 q = 1) (hb : d62130 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62011, d62130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62011, d62130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62012 q = 1) (hb : d62131 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62012, d62131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62012, d62131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62013 q = 1) (hb : d62132 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62013, d62132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62013, d62132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62014 q = 1) (hb : d62133 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62014, d62133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62014, d62133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1740 (p : Pattern) (ha : d62020 p = 1) (hb : d62139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62015 q = 1) (hb : d62134 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62015, d62134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1739 q ha hb
    | true =>
      simp only [d62015, d62134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62016 q = 1) (hb : d62135 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62016, d62135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62016, d62135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62017 q = 1) (hb : d62136 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62017, d62136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62017, d62136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62018 q = 1) (hb : d62137 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62018, d62137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62018, d62137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62019 q = 1) (hb : d62138 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62019, d62138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62019, d62138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62020 q = 1) (hb : d62139 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62020, d62139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62020, d62139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1741 (p : Pattern) (ha : d62026 p = 1) (hb : d62145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62021 q = 1) (hb : d62140 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62021, d62140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1740 q ha hb
    | true =>
      simp only [d62021, d62140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62022 q = 1) (hb : d62141 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62022, d62141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62022, d62141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62023 q = 1) (hb : d62142 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62023, d62142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62023, d62142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62024 q = 1) (hb : d62143 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62024, d62143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62024, d62143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62025 q = 1) (hb : d62144 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62025, d62144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62025, d62144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62026 q = 1) (hb : d62145 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62026, d62145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62026, d62145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1742 (p : Pattern) (ha : d62032 p = 1) (hb : d62151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62027 q = 1) (hb : d62146 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62027, d62146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1741 q ha hb
    | true =>
      simp only [d62027, d62146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62028 q = 1) (hb : d62147 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62028, d62147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62028, d62147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62029 q = 1) (hb : d62148 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62029, d62148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62029, d62148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62030 q = 1) (hb : d62149 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62030, d62149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62030, d62149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62031 q = 1) (hb : d62150 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62031, d62150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62031, d62150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62032 q = 1) (hb : d62151 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62032, d62151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62032, d62151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1743 (p : Pattern) (ha : d54404 p = 1) (hb : d61810 p = 1) : d62153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53638 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53641 q = 1) (hb : d55754 q = 1) : d53641 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53642 q = 1) (hb : d61809 q = 1) : d62152 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d61809, d62152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53642, d61809, d62152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54404 q = 1) (hb : d61810 q = 1) : d62153 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54404, d61810, d62153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54404, d61810, d62153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1744 (p : Pattern) (ha : d54410 p = 1) (hb : d61810 p = 1) : d62160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53654 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53659 q = 1) (hb : d55754 q = 1) : d53659 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53660 q = 1) (hb : d61809 q = 1) : d62159 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d61809, d62159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53660, d61809, d62159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54410 q = 1) (hb : d61810 q = 1) : d62160 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54410, d61810, d62160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54410, d61810, d62160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1745 (p : Pattern) (ha : d54416 p = 1) (hb : d61810 p = 1) : d62166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54405 q = 1) (hb : d61810 q = 1) : d62154 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54405, d62154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54405, d62154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1743 q ha hb
  have h2 (q : Pattern) (ha : d54406 q = 1) (hb : d61810 q = 1) : d62155 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54406, d62155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54406, d62155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54407 q = 1) (hb : d61810 q = 1) : d62156 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54407, d62156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54407, d62156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54408 q = 1) (hb : d61810 q = 1) : d62157 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54408, d62157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54408, d62157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54409 q = 1) (hb : d61810 q = 1) : d62158 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54409, d62158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54409, d62158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54411 q = 1) (hb : d61810 q = 1) : d62161 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54411, d62161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54411, d62161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1744 q ha hb
  have h7 (q : Pattern) (ha : d54412 q = 1) (hb : d61810 q = 1) : d62162 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54412, d62162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54412, d62162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54413 q = 1) (hb : d61810 q = 1) : d62163 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54413, d62163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54413, d62163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54414 q = 1) (hb : d61810 q = 1) : d62164 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54414, d62164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54414, d62164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54415 q = 1) (hb : d61810 q = 1) : d62165 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54415, d62165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54415, d62165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54416 q = 1) (hb : d61810 q = 1) : d62166 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54416, d62166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54416, d62166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro1746 (p : Pattern) (ha : d54417 p = 1) (hb : d61810 p = 1) : d62168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53684 q = 1) (hb : d55754 q = 1) : d53684 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53685 q = 1) (hb : d61809 q = 1) : d62167 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d61809, d62167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53685, d61809, d62167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54417 q = 1) (hb : d61810 q = 1) : d62168 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54417, d61810, d62168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54417, d61810, d62168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1747 (p : Pattern) (ha : d54423 p = 1) (hb : d61810 p = 1) : d62174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54418 q = 1) (hb : d61810 q = 1) : d62169 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54418, d62169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54418, d62169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1746 q ha hb
  have h2 (q : Pattern) (ha : d54419 q = 1) (hb : d61810 q = 1) : d62170 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54419, d62170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54419, d62170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54420 q = 1) (hb : d61810 q = 1) : d62171 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54420, d62171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54420, d62171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54421 q = 1) (hb : d61810 q = 1) : d62172 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54421, d62172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54421, d62172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54422 q = 1) (hb : d61810 q = 1) : d62173 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54422, d62173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54422, d62173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54423 q = 1) (hb : d61810 q = 1) : d62174 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54423, d62174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54423, d62174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1748 (p : Pattern) (ha : d54425 p = 1) (hb : d61810 p = 1) : d62177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53706 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53711 q = 1) (hb : d55754 q = 1) : d53711 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53712 q = 1) (hb : d61809 q = 1) : d62176 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d61809, d62176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53712, d61809, d62176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54425 q = 1) (hb : d61810 q = 1) : d62177 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54425, d61810, d62177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54425, d61810, d62177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro1749 (p : Pattern) (ha : d54431 p = 1) (hb : d61810 p = 1) : d62183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54426 q = 1) (hb : d61810 q = 1) : d62178 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54426, d62178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54426, d62178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1748 q ha hb
  have h2 (q : Pattern) (ha : d54427 q = 1) (hb : d61810 q = 1) : d62179 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54427, d62179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54427, d62179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54428 q = 1) (hb : d61810 q = 1) : d62180 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54428, d62180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54428, d62180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54429 q = 1) (hb : d61810 q = 1) : d62181 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54429, d62181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54429, d62181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54430 q = 1) (hb : d61810 q = 1) : d62182 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54430, d62182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54430, d62182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54431 q = 1) (hb : d61810 q = 1) : d62183 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54431, d62183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54431, d62183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
