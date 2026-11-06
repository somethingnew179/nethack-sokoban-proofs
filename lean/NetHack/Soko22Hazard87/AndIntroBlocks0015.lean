import NetHack.Soko22Hazard87.AndIntroBlocks0014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro3750 (p : Pattern) (ha : d67433 p = 1) (hb : d67742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1012 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro131 q ha hb
    | true =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro132 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4466 q = 1) (hb : d52637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d52637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4466, d52637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67430 q = 1) (hb : d67739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67430, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67430, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67431 q = 1) (hb : d67740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67431, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67431, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67432 q = 1) (hb : d67741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67432, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67432, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67433 q = 1) (hb : d67742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67433, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67433, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3751 (p : Pattern) (ha : d67439 p = 1) (hb : d67748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67418 q = 1) (hb : d67727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67418, d67727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3747 q ha hb
    | true =>
      simp only [d67418, d67727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3748 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d67419 q = 1) (hb : d67728 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67419, d67728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67419, d67728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d67420 q = 1) (hb : d67729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67420, d67729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67420, d67729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d67421 q = 1) (hb : d67730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67421, d67730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67421, d67730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67425 q = 1) (hb : d67734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67425, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67425, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3749 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d67426 q = 1) (hb : d67735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67426, d67735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67426, d67735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d67427 q = 1) (hb : d67736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67427, d67736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67427, d67736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d67428 q = 1) (hb : d67737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67428, d67737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67428, d67737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d67429 q = 1) (hb : d67738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67429, d67738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67429, d67738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67434 q = 1) (hb : d67743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67434, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67434, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3750 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d67435 q = 1) (hb : d67744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67435, d67744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67435, d67744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d67436 q = 1) (hb : d67745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67436, d67745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d67436, d67745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d67437 q = 1) (hb : d67746 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67437, d67746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67437, d67746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d67438 q = 1) (hb : d67747 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67438, d67747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67438, d67747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d67439 q = 1) (hb : d67748 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67439, d67748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67439, d67748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3752 (p : Pattern) (ha : d67445 p = 1) (hb : d67754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67440 q = 1) (hb : d67749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67440, d67749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67440, d67749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3751 q ha hb
  have h2 (q : Pattern) (ha : d67441 q = 1) (hb : d67750 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67441, d67750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67441, d67750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67442 q = 1) (hb : d67751 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67442, d67751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67442, d67751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67443 q = 1) (hb : d67752 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67443, d67752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67443, d67752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67444 q = 1) (hb : d67753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67444, d67753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67444, d67753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67445 q = 1) (hb : d67754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67445, d67754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67445, d67754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3753 (p : Pattern) (ha : d67451 p = 1) (hb : d67760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro186 q ha hb
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67448 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d67449 q = 1) (hb : d67758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67449, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67449, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67450 q = 1) (hb : d67759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67450, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67450, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67451 q = 1) (hb : d67760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67451, d67760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67451, d67760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro3754 (p : Pattern) (ha : d67455 p = 1) (hb : d67764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro186 q ha hb
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67448 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d67449 q = 1) (hb : d67758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67449, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67449, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67450 q = 1) (hb : d67759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67450, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67450, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1328 q = 1) (hb : d52819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro192 q ha hb
    | true =>
      simp only [d1328, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q ha hb
  have h15 (q : Pattern) (ha : d1329 q = 1) (hb : d52820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1330 q = 1) (hb : d52821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1330, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d1331 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1334 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro194 q ha hb
    | true =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h19 (q : Pattern) (ha : d1335 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1336 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d4490 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d67452 q = 1) (hb : d67761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67452, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d67452, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d67453 q = 1) (hb : d67762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67453, d67762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d67453, d67762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d67454 q = 1) (hb : d67763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67454, d67763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d67454, d67763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d67455 q = 1) (hb : d67764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67455, d67764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67455, d67764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro3755 (p : Pattern) (ha : d67462 p = 1) (hb : d67771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4490 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67452 q = 1) (hb : d67761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67452, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67452, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67460 q = 1) (hb : d67769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67460, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67460, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67461 q = 1) (hb : d67770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67461, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67461, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67462 q = 1) (hb : d67771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67462, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67462, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3756 (p : Pattern) (ha : d67471 p = 1) (hb : d67780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1437 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro183 q ha hb
    | true =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro184 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d52931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d52931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4505, d52931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67468 q = 1) (hb : d67777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67468, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67468, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67469 q = 1) (hb : d67778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67469, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67469, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67470 q = 1) (hb : d67779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67470, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67470, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67471 q = 1) (hb : d67780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67471, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67471, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3757 (p : Pattern) (ha : d67477 p = 1) (hb : d67786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67456 q = 1) (hb : d67765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67456, d67765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3753 q ha hb
    | true =>
      simp only [d67456, d67765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3754 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d67457 q = 1) (hb : d67766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67457, d67766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67457, d67766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d67458 q = 1) (hb : d67767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67458, d67767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67458, d67767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d67459 q = 1) (hb : d67768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67459, d67768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67459, d67768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67463 q = 1) (hb : d67772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67463, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67463, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3755 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d67464 q = 1) (hb : d67773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67464, d67773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67464, d67773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d67465 q = 1) (hb : d67774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67465, d67774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67465, d67774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d67466 q = 1) (hb : d67775 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67466, d67775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67466, d67775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d67467 q = 1) (hb : d67776 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67467, d67776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67467, d67776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67472 q = 1) (hb : d67781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67472, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67472, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3756 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d67473 q = 1) (hb : d67782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67473, d67782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67473, d67782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d67474 q = 1) (hb : d67783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67474, d67783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d67474, d67783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d67475 q = 1) (hb : d67784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67475, d67784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67475, d67784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d67476 q = 1) (hb : d67785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67476, d67785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67476, d67785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d67477 q = 1) (hb : d67786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67477, d67786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67477, d67786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3758 (p : Pattern) (ha : d67483 p = 1) (hb : d67792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67478 q = 1) (hb : d67787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67478, d67787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67478, d67787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3757 q ha hb
  have h2 (q : Pattern) (ha : d67479 q = 1) (hb : d67788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67479, d67788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67479, d67788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67480 q = 1) (hb : d67789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67480, d67789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67480, d67789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67481 q = 1) (hb : d67790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67481, d67790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67481, d67790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67482 q = 1) (hb : d67791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67482, d67791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67482, d67791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67483 q = 1) (hb : d67792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67483, d67792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67483, d67792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3759 (p : Pattern) (ha : d67490 p = 1) (hb : d67799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro242 q ha hb
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67487 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d67488 q = 1) (hb : d67797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67488, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67488, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67489 q = 1) (hb : d67798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67489, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67489, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67490 q = 1) (hb : d67799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67490, d67799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67490, d67799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro3760 (p : Pattern) (ha : d67494 p = 1) (hb : d67803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro242 q ha hb
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67487 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d67488 q = 1) (hb : d67797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67488, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67488, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67489 q = 1) (hb : d67798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67489, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67489, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1805 q = 1) (hb : d53134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro248 q ha hb
    | true =>
      simp only [d1805, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q ha hb
  have h15 (q : Pattern) (ha : d1806 q = 1) (hb : d53135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1807 q = 1) (hb : d53136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1807, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d1808 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1811 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro250 q ha hb
    | true =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h19 (q : Pattern) (ha : d1812 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1813 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d4530 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d67491 q = 1) (hb : d67800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67491, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d67491, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d67492 q = 1) (hb : d67801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67492, d67801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d67492, d67801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d67493 q = 1) (hb : d67802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67493, d67802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d67493, d67802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d67494 q = 1) (hb : d67803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67494, d67803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67494, d67803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro3761 (p : Pattern) (ha : d67501 p = 1) (hb : d67810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67491 q = 1) (hb : d67800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67491, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67491, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67499 q = 1) (hb : d67808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67499, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67499, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67500 q = 1) (hb : d67809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67500, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67500, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67501 q = 1) (hb : d67810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67501, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67501, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3762 (p : Pattern) (ha : d67510 p = 1) (hb : d67819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1914 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro239 q ha hb
    | true =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro240 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d53246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d53246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4545, d53246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67507 q = 1) (hb : d67816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67507, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67507, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67508 q = 1) (hb : d67817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67508, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67508, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67509 q = 1) (hb : d67818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67509, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67509, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67510 q = 1) (hb : d67819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67510, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67510, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3763 (p : Pattern) (ha : d67516 p = 1) (hb : d67825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67495 q = 1) (hb : d67804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67495, d67804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3759 q ha hb
    | true =>
      simp only [d67495, d67804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3760 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d67496 q = 1) (hb : d67805 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67496, d67805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67496, d67805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d67497 q = 1) (hb : d67806 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67497, d67806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67497, d67806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d67498 q = 1) (hb : d67807 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67498, d67807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67498, d67807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67502 q = 1) (hb : d67811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67502, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67502, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3761 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d67503 q = 1) (hb : d67812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67503, d67812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67503, d67812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d67504 q = 1) (hb : d67813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67504, d67813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67504, d67813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d67505 q = 1) (hb : d67814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67505, d67814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67505, d67814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d67506 q = 1) (hb : d67815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67506, d67815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67506, d67815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67511 q = 1) (hb : d67820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67511, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67511, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3762 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d67512 q = 1) (hb : d67821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67512, d67821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67512, d67821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d67513 q = 1) (hb : d67822 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67513, d67822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d67513, d67822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d67514 q = 1) (hb : d67823 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67514, d67823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67514, d67823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d67515 q = 1) (hb : d67824 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67515, d67824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67515, d67824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d67516 q = 1) (hb : d67825 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67516, d67825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67516, d67825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3764 (p : Pattern) (ha : d67522 p = 1) (hb : d67831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67517 q = 1) (hb : d67826 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67517, d67826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67517, d67826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3763 q ha hb
  have h2 (q : Pattern) (ha : d67518 q = 1) (hb : d67827 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67518, d67827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67518, d67827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67519 q = 1) (hb : d67828 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67519, d67828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67519, d67828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67520 q = 1) (hb : d67829 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67520, d67829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67520, d67829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67521 q = 1) (hb : d67830 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67521, d67830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67521, d67830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67522 q = 1) (hb : d67831 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67522, d67831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67522, d67831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3765 (p : Pattern) (ha : d67530 p = 1) (hb : d67839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro301 q ha hb
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67527 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d67528 q = 1) (hb : d67837 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67528, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67528, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67529 q = 1) (hb : d67838 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67529, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67529, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67530 q = 1) (hb : d67839 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67530, d67839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67530, d67839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro3766 (p : Pattern) (ha : d67534 p = 1) (hb : d67843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro301 q ha hb
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67527 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d67528 q = 1) (hb : d67837 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67528, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67528, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67529 q = 1) (hb : d67838 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67529, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67529, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2283 q = 1) (hb : d53451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro307 q ha hb
    | true =>
      simp only [d2283, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q ha hb
  have h15 (q : Pattern) (ha : d2284 q = 1) (hb : d53452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2285 q = 1) (hb : d53453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2285, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d2286 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2289 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro309 q ha hb
    | true =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h19 (q : Pattern) (ha : d2290 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d2291 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d4571 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d67531 q = 1) (hb : d67840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67531, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d67531, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d67532 q = 1) (hb : d67841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67532, d67841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d67532, d67841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d67533 q = 1) (hb : d67842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67533, d67842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d67533, d67842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d67534 q = 1) (hb : d67843 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67534, d67843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67534, d67843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro3767 (p : Pattern) (ha : d67541 p = 1) (hb : d67850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67531 q = 1) (hb : d67840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67531, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67531, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67539 q = 1) (hb : d67848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67539, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67539, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67540 q = 1) (hb : d67849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67540, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67540, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67541 q = 1) (hb : d67850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67541, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67541, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3768 (p : Pattern) (ha : d67550 p = 1) (hb : d67859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2392 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro298 q ha hb
    | true =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro299 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d53563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d53563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4586, d53563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67547 q = 1) (hb : d67856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67547, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d67547, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67548 q = 1) (hb : d67857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67548, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67548, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67549 q = 1) (hb : d67858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67549, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67549, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67550 q = 1) (hb : d67859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67550, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67550, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3769 (p : Pattern) (ha : d67556 p = 1) (hb : d67865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67535 q = 1) (hb : d67844 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67535, d67844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3765 q ha hb
    | true =>
      simp only [d67535, d67844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3766 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d67536 q = 1) (hb : d67845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67536, d67845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67536, d67845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d67537 q = 1) (hb : d67846 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67537, d67846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67537, d67846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d67538 q = 1) (hb : d67847 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67538, d67847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67538, d67847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67542 q = 1) (hb : d67851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67542, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67542, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3767 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d67543 q = 1) (hb : d67852 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67543, d67852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67543, d67852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d67544 q = 1) (hb : d67853 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67544, d67853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67544, d67853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d67545 q = 1) (hb : d67854 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67545, d67854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67545, d67854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d67546 q = 1) (hb : d67855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67546, d67855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67546, d67855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67551 q = 1) (hb : d67860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67551, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67551, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3768 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d67552 q = 1) (hb : d67861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67552, d67861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67552, d67861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d67553 q = 1) (hb : d67862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67553, d67862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d67553, d67862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d67554 q = 1) (hb : d67863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67554, d67863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67554, d67863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d67555 q = 1) (hb : d67864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67555, d67864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67555, d67864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d67556 q = 1) (hb : d67865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67556, d67865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67556, d67865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3770 (p : Pattern) (ha : d67562 p = 1) (hb : d67871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67557 q = 1) (hb : d67866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67557, d67866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67557, d67866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3769 q ha hb
  have h2 (q : Pattern) (ha : d67558 q = 1) (hb : d67867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67558, d67867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67558, d67867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67559 q = 1) (hb : d67868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67559, d67868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67559, d67868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67560 q = 1) (hb : d67869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67560, d67869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67560, d67869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67561 q = 1) (hb : d67870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67561, d67870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67561, d67870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67562 q = 1) (hb : d67871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67562, d67871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67562, d67871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3771 (p : Pattern) (ha : d67568 p = 1) (hb : d67877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d67409 q = 1) (hb : d67718 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67409, d67718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3740 q ha hb
    | true =>
      simp only [d67409, d67718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3746 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d67446 q = 1) (hb : d67755 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67446, d67755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67446, d67755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3752 q ha hb
  have h3 (q : Pattern) (ha : d67447 q = 1) (hb : d67756 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67447, d67756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67447, d67756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67484 q = 1) (hb : d67793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67484, d67793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67484, d67793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3758 q ha hb
  have h5 (q : Pattern) (ha : d67485 q = 1) (hb : d67794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67485, d67794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67485, d67794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67486 q = 1) (hb : d67795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67486, d67795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67486, d67795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67523 q = 1) (hb : d67832 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67523, d67832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67523, d67832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3764 q ha hb
  have h8 (q : Pattern) (ha : d67524 q = 1) (hb : d67833 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67524, d67833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67524, d67833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67525 q = 1) (hb : d67834 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67525, d67834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67525, d67834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67526 q = 1) (hb : d67835 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67526, d67835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67526, d67835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67563 q = 1) (hb : d67872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67563, d67872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67563, d67872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3770 q ha hb
  have h12 (q : Pattern) (ha : d67564 q = 1) (hb : d67873 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67564, d67873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67564, d67873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67565 q = 1) (hb : d67874 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67565, d67874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67565, d67874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67566 q = 1) (hb : d67875 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67566, d67875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67566, d67875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67567 q = 1) (hb : d67876 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d67567, d67876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67567, d67876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67568 q = 1) (hb : d67877 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d67568, d67877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67568, d67877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro3772 (p : Pattern) (ha : d67574 p = 1) (hb : d67883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67569 q = 1) (hb : d67878 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d67569, d67878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3771 q ha hb
    | true =>
      simp only [d67569, d67878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67570 q = 1) (hb : d67879 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d67570, d67879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67570, d67879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67571 q = 1) (hb : d67880 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d67571, d67880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67571, d67880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67572 q = 1) (hb : d67881 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d67572, d67881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67572, d67881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67573 q = 1) (hb : d67882 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d67573, d67882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67573, d67882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67574 q = 1) (hb : d67883 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d67574, d67883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67574, d67883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3773 (p : Pattern) (ha : d67580 p = 1) (hb : d67889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67575 q = 1) (hb : d67884 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d67575, d67884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3772 q ha hb
    | true =>
      simp only [d67575, d67884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67576 q = 1) (hb : d67885 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d67576, d67885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67576, d67885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67577 q = 1) (hb : d67886 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d67577, d67886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67577, d67886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67578 q = 1) (hb : d67887 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d67578, d67887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67578, d67887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67579 q = 1) (hb : d67888 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d67579, d67888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67579, d67888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67580 q = 1) (hb : d67889 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d67580, d67889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67580, d67889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3774 (p : Pattern) (ha : d67586 p = 1) (hb : d67895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67581 q = 1) (hb : d67890 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d67581, d67890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3773 q ha hb
    | true =>
      simp only [d67581, d67890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67582 q = 1) (hb : d67891 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d67582, d67891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67582, d67891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67583 q = 1) (hb : d67892 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d67583, d67892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67583, d67892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67584 q = 1) (hb : d67893 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d67584, d67893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67584, d67893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67585 q = 1) (hb : d67894 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d67585, d67894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67585, d67894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67586 q = 1) (hb : d67895 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d67586, d67895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67586, d67895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3775 (p : Pattern) (ha : d67592 p = 1) (hb : d67901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67587 q = 1) (hb : d67896 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d67587, d67896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3774 q ha hb
    | true =>
      simp only [d67587, d67896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67588 q = 1) (hb : d67897 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d67588, d67897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67588, d67897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67589 q = 1) (hb : d67898 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d67589, d67898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67589, d67898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67590 q = 1) (hb : d67899 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d67590, d67899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67590, d67899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67591 q = 1) (hb : d67900 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d67591, d67900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67591, d67900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67592 q = 1) (hb : d67901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d67592, d67901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67592, d67901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3776 (p : Pattern) (ha : d67598 p = 1) (hb : d67907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67593 q = 1) (hb : d67902 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d67593, d67902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3775 q ha hb
    | true =>
      simp only [d67593, d67902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67594 q = 1) (hb : d67903 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d67594, d67903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67594, d67903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67595 q = 1) (hb : d67904 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d67595, d67904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67595, d67904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67596 q = 1) (hb : d67905 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67596, d67905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67596, d67905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67597 q = 1) (hb : d67906 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d67597, d67906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67597, d67906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67598 q = 1) (hb : d67907 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d67598, d67907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67598, d67907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3777 (p : Pattern) (ha : d67604 p = 1) (hb : d67913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67599 q = 1) (hb : d67908 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d67599, d67908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3776 q ha hb
    | true =>
      simp only [d67599, d67908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67600 q = 1) (hb : d67909 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d67600, d67909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67600, d67909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67601 q = 1) (hb : d67910 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67601, d67910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67601, d67910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67602 q = 1) (hb : d67911 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d67602, d67911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67602, d67911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67603 q = 1) (hb : d67912 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d67603, d67912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67603, d67912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67604 q = 1) (hb : d67913 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d67604, d67913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67604, d67913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3778 (p : Pattern) (ha : d67610 p = 1) (hb : d67919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67605 q = 1) (hb : d67914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d67605, d67914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3777 q ha hb
    | true =>
      simp only [d67605, d67914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67606 q = 1) (hb : d67915 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d67606, d67915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67606, d67915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67607 q = 1) (hb : d67916 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d67607, d67916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67607, d67916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67608 q = 1) (hb : d67917 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d67608, d67917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67608, d67917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67609 q = 1) (hb : d67918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d67609, d67918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67609, d67918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67610 q = 1) (hb : d67919 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d67610, d67919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67610, d67919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro3779 (p : Pattern) (ha : d53865 p = 1) (hb : d67301 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d67301 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro3780 (p : Pattern) (ha : d104 p = 1) (hb : d67305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d67302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d67302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d67302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d67303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d67303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d67303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d67304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d67304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d67304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d104 q = 1) (hb : d67305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d67305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d67305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3781 (p : Pattern) (ha : d111 p = 1) (hb : d67309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d67302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d67302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d67302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d67303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d67303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d67303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d67304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d67304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d67304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108 q = 1) (hb : d67306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d67306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d67306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d109 q = 1) (hb : d67307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d67307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d67307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d110 q = 1) (hb : d67308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d67308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d67308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d111 q = 1) (hb : d67309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d67309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d67309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3782 (p : Pattern) (ha : d406 p = 1) (hb : d67316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
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
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d67306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d67306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d67306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d67314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d67314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d67314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d67315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d67315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d67315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d67316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d67316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d67316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3783 (p : Pattern) (ha : d462 p = 1) (hb : d67325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d52063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d52063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d52063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d67322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d67322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d67322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d67323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d67323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d67323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d67324 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d67324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d67324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d67325 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d67325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d67325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3784 (p : Pattern) (ha : d53647 p = 1) (hb : d67331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d67310 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d67310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3780 q ha hb
    | true =>
      simp only [d112, d67310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3781 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d67311 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d67311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d67311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d67312 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d67312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d67312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d67313 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d67313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d67313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d67317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d67317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d67317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3782 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d67318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d67318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d67318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d67319 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d67319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d67319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d67320 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d67320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d67320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d67321 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d67321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d67321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d67326 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d67326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d67326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3783 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d67327 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d67327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d67327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d67328 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d67328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d67328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d67329 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d67329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d67329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d67330 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d67330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d67330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d67331 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d67331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d67331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3785 (p : Pattern) (ha : d284 p = 1) (hb : d67340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d280 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d67337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d67337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281, d67337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d67338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d67338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282, d67338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d67339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d67339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d283, d67339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d284 q = 1) (hb : d67340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d67340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d67340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3786 (p : Pattern) (ha : d291 p = 1) (hb : d67344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d67337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d67337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d67337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d67338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d67338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d67338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d67339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d67339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d67339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d287 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d287, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288 q = 1) (hb : d67341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d67341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288, d67341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d289 q = 1) (hb : d67342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d67342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289, d67342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290 q = 1) (hb : d67343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d67343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290, d67343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d291 q = 1) (hb : d67344 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d67344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d291, d67344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3787 (p : Pattern) (ha : d53655 p = 1) (hb : d67351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d67341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d67341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d67341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d67349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d67349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d67349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d67350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d67350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d67350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d67351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d67351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d67351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3788 (p : Pattern) (ha : d53665 p = 1) (hb : d67360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d53661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52197, d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d67357 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d67357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53662, d67357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d67358 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d67358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d67358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d67359 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d67359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d67359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d67360 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d67360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d67360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3789 (p : Pattern) (ha : d53671 p = 1) (hb : d67366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d67345 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d67345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3785 q ha hb
    | true =>
      simp only [d292, d67345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3786 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d67346 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d67346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d67346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53653 q = 1) (hb : d67347 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d67347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, d67347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d67348 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d67348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d67348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53656 q = 1) (hb : d67352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d67352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53656, d67352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3787 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53657 q = 1) (hb : d67353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d67353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53657, d67353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53658 q = 1) (hb : d67354 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d67354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53658, d67354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53659 q = 1) (hb : d67355 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d67355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53659, d67355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53660 q = 1) (hb : d67356 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d67356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53660, d67356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53666 q = 1) (hb : d67361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d67361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53666, d67361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3788 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53667 q = 1) (hb : d67362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d67362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53667, d67362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53668 q = 1) (hb : d67363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d67363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53668, d67363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53669 q = 1) (hb : d67364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d67364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53669, d67364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53670 q = 1) (hb : d67365 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d67365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53670, d67365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53671 q = 1) (hb : d67366 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d67366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53671, d67366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3790 (p : Pattern) (ha : d53677 p = 1) (hb : d67372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d67332 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d67332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d67332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3784 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d67333 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d67333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d67333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d67334 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d67334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d67334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d67335 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d67335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d67335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d67336 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d67336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d67336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53672 q = 1) (hb : d67367 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d67367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d67367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3789 q ha hb
  have h8 (q : Pattern) (ha : d53673 q = 1) (hb : d67368 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d67368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d67368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53674 q = 1) (hb : d67369 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d67369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d67369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53675 q = 1) (hb : d67370 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d67370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d67370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53676 q = 1) (hb : d67371 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d67371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d67371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53677 q = 1) (hb : d67372 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d67372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53677, d67372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3791 (p : Pattern) (ha : d497 p = 1) (hb : d67376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h5 (q : Pattern) (ha : d493 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d67373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d67373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d494, d67373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d67374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d67374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d495, d67374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d67375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d67375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d496, d67375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d497 q = 1) (hb : d67376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d67376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d67376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3792 (p : Pattern) (ha : d507 p = 1) (hb : d67380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d67373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d67373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d67373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d67374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d67374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d67374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d67375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d67375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d67375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d502 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d502, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h13 (q : Pattern) (ha : d503 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d503, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d504 q = 1) (hb : d67377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d67377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d504, d67377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d505 q = 1) (hb : d67378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d67378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d505, d67378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d506 q = 1) (hb : d67379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d67379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d506, d67379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d507 q = 1) (hb : d67380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d67380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d507, d67380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3793 (p : Pattern) (ha : d53680 p = 1) (hb : d67387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d502 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d502, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d504 q = 1) (hb : d67377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d67377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, d67377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d505 q = 1) (hb : d67385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d67385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d67385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d506 q = 1) (hb : d67386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d67386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d67386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53680 q = 1) (hb : d67387 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d67387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d67387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3794 (p : Pattern) (ha : d53691 p = 1) (hb : d67396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52399 q = 1) (hb : d53686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52399, d53686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85 q hb ha
    | true =>
      simp only [d52399, d53686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d52400 q = 1) (hb : d53687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52400, d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53688 q = 1) (hb : d67393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d67393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53688, d67393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53689 q = 1) (hb : d67394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d67394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d67394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53690 q = 1) (hb : d67395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d67395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d67395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53691 q = 1) (hb : d67396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d67396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d67396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3795 (p : Pattern) (ha : d53697 p = 1) (hb : d67402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d67381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d67381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3791 q ha hb
    | true =>
      simp only [d508, d67381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3792 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d67382 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d67382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d67382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53678 q = 1) (hb : d67383 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d67383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, d67383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d67384 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d67384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d67384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53681 q = 1) (hb : d67388 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d67388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53681, d67388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3793 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53682 q = 1) (hb : d67389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d67389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53682, d67389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53683 q = 1) (hb : d67390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d67390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53683, d67390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53684 q = 1) (hb : d67391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d67391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53684, d67391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53685 q = 1) (hb : d67392 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d67392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53685, d67392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53692 q = 1) (hb : d67397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d67397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53692, d67397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3794 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53693 q = 1) (hb : d67398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d67398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53693, d67398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53694 q = 1) (hb : d67399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d67399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53694, d67399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53695 q = 1) (hb : d67400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d67400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53695, d67400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53696 q = 1) (hb : d67401 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d67401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53696, d67401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53697 q = 1) (hb : d67402 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d67402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53697, d67402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3796 (p : Pattern) (ha : d53703 p = 1) (hb : d67408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d67403 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d67403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d67403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3795 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d67404 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d67404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d67404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d67405 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d67405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d67405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d67406 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d67406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d67406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d67407 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d67407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d67407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d67408 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d67408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d67408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3797 (p : Pattern) (ha : d789 p = 1) (hb : d67413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h5 (q : Pattern) (ha : d785 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d67410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d67410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d786, d67410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d67411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d67411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d787, d67411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d67412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d67412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d788, d67412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d789 q = 1) (hb : d67413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d67413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d67413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3798 (p : Pattern) (ha : d799 p = 1) (hb : d67417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d67410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d67410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d67410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d67411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d67411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d67411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d67412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d67412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d67412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d794 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d794, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h13 (q : Pattern) (ha : d795 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d795, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d796 q = 1) (hb : d67414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d67414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d796, d67414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d797 q = 1) (hb : d67415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d67415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d797, d67415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d798 q = 1) (hb : d67416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d67416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d798, d67416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d799 q = 1) (hb : d67417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d67417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d799, d67417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3799 (p : Pattern) (ha : d53707 p = 1) (hb : d67424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d794 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d794, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d796 q = 1) (hb : d67414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d67414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, d67414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d797 q = 1) (hb : d67422 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d67422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d67422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d798 q = 1) (hb : d67423 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d67423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d67423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53707 q = 1) (hb : d67424 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d67424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d67424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3800 (p : Pattern) (ha : d53718 p = 1) (hb : d67433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52636 q = 1) (hb : d53713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52636, d53713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro132 q hb ha
    | true =>
      simp only [d52636, d53713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d52637 q = 1) (hb : d53714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52637, d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53715 q = 1) (hb : d67430 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d67430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53715, d67430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53716 q = 1) (hb : d67431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d67431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d67431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53717 q = 1) (hb : d67432 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d67432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d67432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53718 q = 1) (hb : d67433 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d67433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d67433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3801 (p : Pattern) (ha : d53724 p = 1) (hb : d67439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d67418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d67418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3797 q ha hb
    | true =>
      simp only [d800, d67418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d67419 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d67419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d67419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53705 q = 1) (hb : d67420 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d67420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, d67420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d67421 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d67421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d67421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53708 q = 1) (hb : d67425 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d67425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53708, d67425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3799 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53709 q = 1) (hb : d67426 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d67426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53709, d67426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53710 q = 1) (hb : d67427 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d67427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53710, d67427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53711 q = 1) (hb : d67428 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d67428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53711, d67428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53712 q = 1) (hb : d67429 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d67429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53712, d67429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53719 q = 1) (hb : d67434 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d67434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53719, d67434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3800 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53720 q = 1) (hb : d67435 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d67435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53720, d67435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53721 q = 1) (hb : d67436 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d67436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53721, d67436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53722 q = 1) (hb : d67437 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d67437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53722, d67437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53723 q = 1) (hb : d67438 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d67438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53723, d67438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53724 q = 1) (hb : d67439 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d67439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53724, d67439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3802 (p : Pattern) (ha : d53730 p = 1) (hb : d67445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d67440 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d67440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d67440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3801 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d67441 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d67441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d67441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d67442 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d67442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d67442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d67443 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d67443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d67443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d67444 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d67444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d67444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d67445 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d67445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d67445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3803 (p : Pattern) (ha : d1168 p = 1) (hb : d67451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h5 (q : Pattern) (ha : d1164 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d67448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d67448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1165, d67448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d67449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d67449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1166, d67449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d67450 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d67450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1167, d67450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1168 q = 1) (hb : d67451 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d67451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d67451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3804 (p : Pattern) (ha : d1178 p = 1) (hb : d67455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d67448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d67448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d67448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d67449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d67449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d67449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d67450 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d67450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d67450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1173 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1173, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h13 (q : Pattern) (ha : d1174 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1174, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1175 q = 1) (hb : d67452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d67452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1175, d67452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d1176 q = 1) (hb : d67453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d67453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1176, d67453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1177 q = 1) (hb : d67454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d67454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1177, d67454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1178 q = 1) (hb : d67455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d67455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1178, d67455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3805 (p : Pattern) (ha : d53735 p = 1) (hb : d67462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1173 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1173, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1175 q = 1) (hb : d67452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d67452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, d67452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1176 q = 1) (hb : d67460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d67460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d67460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1177 q = 1) (hb : d67461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d67461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d67461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53735 q = 1) (hb : d67462 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d67462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d67462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3806 (p : Pattern) (ha : d53746 p = 1) (hb : d67471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d53741 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d53741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro184 q hb ha
    | true =>
      simp only [d52930, d53741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d53742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53743 q = 1) (hb : d67468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d67468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53743, d67468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53744 q = 1) (hb : d67469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d67469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d67469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53745 q = 1) (hb : d67470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d67470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d67470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53746 q = 1) (hb : d67471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d67471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d67471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3807 (p : Pattern) (ha : d53752 p = 1) (hb : d67477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d67456 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d67456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3803 q ha hb
    | true =>
      simp only [d1179, d67456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d67457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d67457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d67457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53733 q = 1) (hb : d67458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d67458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, d67458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d67459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d67459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d67459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53736 q = 1) (hb : d67463 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d67463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53736, d67463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3805 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53737 q = 1) (hb : d67464 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d67464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53737, d67464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53738 q = 1) (hb : d67465 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d67465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53738, d67465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53739 q = 1) (hb : d67466 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d67466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53739, d67466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53740 q = 1) (hb : d67467 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d67467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53740, d67467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53747 q = 1) (hb : d67472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d67472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53747, d67472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3806 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53748 q = 1) (hb : d67473 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d67473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53748, d67473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53749 q = 1) (hb : d67474 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d67474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53749, d67474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53750 q = 1) (hb : d67475 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d67475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53750, d67475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53751 q = 1) (hb : d67476 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d67476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53751, d67476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53752 q = 1) (hb : d67477 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d67477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53752, d67477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3808 (p : Pattern) (ha : d53758 p = 1) (hb : d67483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d67478 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d67478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d67478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3807 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d67479 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d67479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d67479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d67480 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d67480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d67480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d67481 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d67481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d67481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d67482 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d67482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d67482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d67483 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d67483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d67483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3809 (p : Pattern) (ha : d1629 p = 1) (hb : d67490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h5 (q : Pattern) (ha : d1625 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d67487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d67487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1626, d67487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d67488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d67488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1627, d67488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d67489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d67489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1628, d67489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1629 q = 1) (hb : d67490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d67490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d67490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3810 (p : Pattern) (ha : d1639 p = 1) (hb : d67494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d67487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d67487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d67487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d67488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d67488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d67488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d67489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d67489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d67489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1634 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1634, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h13 (q : Pattern) (ha : d1635 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1635, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1636 q = 1) (hb : d67491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d67491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1636, d67491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d1637 q = 1) (hb : d67492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d67492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1637, d67492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1638 q = 1) (hb : d67493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d67493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1638, d67493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1639 q = 1) (hb : d67494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d67494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1639, d67494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3811 (p : Pattern) (ha : d53764 p = 1) (hb : d67501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1634 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1634, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1636 q = 1) (hb : d67491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d67491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, d67491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1637 q = 1) (hb : d67499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d67499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d67499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1638 q = 1) (hb : d67500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d67500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d67500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53764 q = 1) (hb : d67501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d67501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d67501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3812 (p : Pattern) (ha : d53775 p = 1) (hb : d67510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d53770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d53770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro240 q hb ha
    | true =>
      simp only [d53245, d53770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d53771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53772 q = 1) (hb : d67507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d67507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53772, d67507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53773 q = 1) (hb : d67508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d67508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d67508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53774 q = 1) (hb : d67509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d67509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d67509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53775 q = 1) (hb : d67510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d67510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d67510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3813 (p : Pattern) (ha : d53781 p = 1) (hb : d67516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d67495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d67495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3809 q ha hb
    | true =>
      simp only [d1640, d67495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3810 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d67496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d67496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d67496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d67497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d67497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, d67497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d67498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d67498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d67498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53765 q = 1) (hb : d67502 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d67502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53765, d67502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3811 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53766 q = 1) (hb : d67503 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d67503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53766, d67503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53767 q = 1) (hb : d67504 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d67504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53767, d67504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53768 q = 1) (hb : d67505 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d67505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53768, d67505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53769 q = 1) (hb : d67506 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d67506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53769, d67506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53776 q = 1) (hb : d67511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d67511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53776, d67511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3812 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53777 q = 1) (hb : d67512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d67512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53777, d67512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53778 q = 1) (hb : d67513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d67513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53778, d67513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53779 q = 1) (hb : d67514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d67514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53779, d67514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53780 q = 1) (hb : d67515 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d67515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53780, d67515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53781 q = 1) (hb : d67516 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d67516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53781, d67516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3814 (p : Pattern) (ha : d53787 p = 1) (hb : d67522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d67517 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d67517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d67517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3813 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d67518 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d67518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d67518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d67519 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d67519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d67519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d67520 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d67520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d67520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d67521 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d67521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d67521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d67522 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d67522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d67522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3815 (p : Pattern) (ha : d2112 p = 1) (hb : d67530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h5 (q : Pattern) (ha : d2108 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d67527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d67527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2109, d67527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d67528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d67528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2110, d67528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d67529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d67529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2111, d67529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2112 q = 1) (hb : d67530 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d67530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d67530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3816 (p : Pattern) (ha : d2122 p = 1) (hb : d67534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d67527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d67527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d67527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d67528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d67528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d67528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d67529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d67529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d67529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2117 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2117, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h13 (q : Pattern) (ha : d2118 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2118, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2119 q = 1) (hb : d67531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d67531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2119, d67531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d2120 q = 1) (hb : d67532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d67532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2120, d67532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2121 q = 1) (hb : d67533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d67533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2121, d67533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2122 q = 1) (hb : d67534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d67534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2122, d67534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3817 (p : Pattern) (ha : d53794 p = 1) (hb : d67541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2117 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2117, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h3 (q : Pattern) (ha : d2118 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2119 q = 1) (hb : d67531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d67531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2119, d67531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2120 q = 1) (hb : d67539 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d67539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d67539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2121 q = 1) (hb : d67540 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d67540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d67540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53794 q = 1) (hb : d67541 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d67541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d67541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3818 (p : Pattern) (ha : d53805 p = 1) (hb : d67550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d53800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d53800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro299 q hb ha
    | true =>
      simp only [d53562, d53800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d53801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53802 q = 1) (hb : d67547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d67547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53802, d67547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53803 q = 1) (hb : d67548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d67548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d67548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53804 q = 1) (hb : d67549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d67549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d67549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53805 q = 1) (hb : d67550 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d67550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d67550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3819 (p : Pattern) (ha : d53811 p = 1) (hb : d67556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d67535 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d67535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3815 q ha hb
    | true =>
      simp only [d2123, d67535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3816 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d67536 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d67536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d67536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d67537 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d67537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, d67537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d67538 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d67538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d67538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53795 q = 1) (hb : d67542 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d67542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53795, d67542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3817 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53796 q = 1) (hb : d67543 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d67543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53796, d67543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53797 q = 1) (hb : d67544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d67544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53797, d67544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53798 q = 1) (hb : d67545 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d67545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53798, d67545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53799 q = 1) (hb : d67546 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d67546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53799, d67546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53806 q = 1) (hb : d67551 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d67551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53806, d67551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3818 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53807 q = 1) (hb : d67552 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d67552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53807, d67552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53808 q = 1) (hb : d67553 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d67553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53808, d67553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53809 q = 1) (hb : d67554 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d67554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53809, d67554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53810 q = 1) (hb : d67555 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d67555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53810, d67555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53811 q = 1) (hb : d67556 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d67556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53811, d67556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3820 (p : Pattern) (ha : d53817 p = 1) (hb : d67562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d67557 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d67557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d67557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3819 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d67558 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d67558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d67558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d67559 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d67559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d67559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d67560 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d67560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d67560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d67561 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d67561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d67561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d67562 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d67562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d67562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3821 (p : Pattern) (ha : d53823 p = 1) (hb : d67568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d67409 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d67409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3790 q ha hb
    | true =>
      simp only [d53704, d67409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3796 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d67446 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d67446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d67446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3802 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d67447 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d67447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d67447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d67484 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d67484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d67484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3808 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d67485 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d67485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d67485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d67486 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d67486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d67486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d67523 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d67523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d67523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3814 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d67524 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d67524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d67524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d67525 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d67525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d67525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d67526 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d67526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d67526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d67563 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d67563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d67563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3820 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d67564 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d67564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d67564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d67565 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d67565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d67565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d67566 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d67566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d67566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d67567 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d67567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d67567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d67568 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d67568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d67568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3822 (p : Pattern) (ha : d53829 p = 1) (hb : d67574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d67569 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d67569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3821 q ha hb
    | true =>
      simp only [d53824, d67569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d67570 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d67570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d67570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d67571 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d67571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d67571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d67572 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d67572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d67572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d67573 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d67573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d67573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d67574 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d67574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d67574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3823 (p : Pattern) (ha : d53835 p = 1) (hb : d67580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d67575 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d67575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3822 q ha hb
    | true =>
      simp only [d53830, d67575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d67576 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d67576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d67576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d67577 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d67577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d67577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d67578 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d67578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d67578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d67579 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d67579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d67579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d67580 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d67580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d67580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3824 (p : Pattern) (ha : d53841 p = 1) (hb : d67586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d67581 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d67581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3823 q ha hb
    | true =>
      simp only [d53836, d67581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d67582 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d67582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d67582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d67583 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d67583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d67583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d67584 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d67584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d67584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d67585 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d67585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d67585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d67586 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d67586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d67586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3825 (p : Pattern) (ha : d53847 p = 1) (hb : d67592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d67587 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d67587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3824 q ha hb
    | true =>
      simp only [d53842, d67587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d67588 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d67588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d67588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d67589 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d67589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d67589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d67590 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d67590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d67590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d67591 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d67591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d67591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d67592 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d67592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d67592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3826 (p : Pattern) (ha : d53853 p = 1) (hb : d67598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d67593 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d67593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3825 q ha hb
    | true =>
      simp only [d53848, d67593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d67594 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d67594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d67594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d67595 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d67595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d67595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d67596 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d67596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d67596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d67597 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d67597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d67597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d67598 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d67598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d67598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3827 (p : Pattern) (ha : d53859 p = 1) (hb : d67604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d67599 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d67599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3826 q ha hb
    | true =>
      simp only [d53854, d67599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d67600 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d67600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d67600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d67601 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d67601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d67601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d67602 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d67602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d67602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d67603 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d67603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d67603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d67604 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d67604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d67604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3828 (p : Pattern) (ha : d53865 p = 1) (hb : d67610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d67605 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d67605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3827 q ha hb
    | true =>
      simp only [d53860, d67605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d67606 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d67606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d67606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d67607 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d67607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d67607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d67608 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d67608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d67608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d67609 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d67609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d67609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d67610 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d67610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d67610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3829 (p : Pattern) (ha : d104 p = 1) (hb : d67614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d67611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d67612 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d67612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d67612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d67613 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d67613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d67613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d104 q = 1) (hb : d67614 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d67614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d67614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3830 (p : Pattern) (ha : d111 p = 1) (hb : d67618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d67611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d67612 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d67612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d67612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d67613 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d67613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d67613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d4340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d108 q = 1) (hb : d67615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d109 q = 1) (hb : d67616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d67616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d67616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d110 q = 1) (hb : d67617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d67617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d67617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d111 q = 1) (hb : d67618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d67618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d67618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3831 (p : Pattern) (ha : d406 p = 1) (hb : d67625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d4340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d67615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d67623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d67624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d67625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d67625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d67625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3832 (p : Pattern) (ha : d462 p = 1) (hb : d67634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d4355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d4355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d4355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d67631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d67631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d67631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d67632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d67632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d67632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d67633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d67633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d67633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d67634 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d67634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d67634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3833 (p : Pattern) (ha : d53647 p = 1) (hb : d67640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d67619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d67619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3829 q ha hb
    | true =>
      simp only [d112, d67619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3830 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d67620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d67620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d67620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d67621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d67621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d67621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d67622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d67622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d67622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d67626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3831 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d67627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d67628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d67629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d67630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d67630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d67630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d67635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3832 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d67636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d67637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d67638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d67639 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d67640 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d67640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d67640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3834 (p : Pattern) (ha : d284 p = 1) (hb : d67649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d280 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d67646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d67647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d67648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d283, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d284 q = 1) (hb : d67649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d67649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d67649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3835 (p : Pattern) (ha : d291 p = 1) (hb : d67653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d67646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d67647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d67648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d287 q = 1) (hb : d4376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d4376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d287, d4376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d288 q = 1) (hb : d67650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d289 q = 1) (hb : d67651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d67651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289, d67651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290 q = 1) (hb : d67652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d67652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290, d67652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d291 q = 1) (hb : d67653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d67653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d291, d67653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3836 (p : Pattern) (ha : d53655 p = 1) (hb : d67660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d4376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d4376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d4376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d67650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d67658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d67659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d67660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3837 (p : Pattern) (ha : d53665 p = 1) (hb : d67669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d430 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4391 q = 1) (hb : d53661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4391, d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d67666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d67666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53662, d67666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d67667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d67668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d67669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3838 (p : Pattern) (ha : d53671 p = 1) (hb : d67675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d67654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d67654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3834 q ha hb
    | true =>
      simp only [d292, d67654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3835 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d67655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d67655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d67655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53653 q = 1) (hb : d67656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d67656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, d67656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d67657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d67657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d67657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53656 q = 1) (hb : d67661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53656, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3836 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53657 q = 1) (hb : d67662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d67662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53657, d67662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53658 q = 1) (hb : d67663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d67663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53658, d67663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53659 q = 1) (hb : d67664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d67664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53659, d67664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53660 q = 1) (hb : d67665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d67665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53660, d67665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53666 q = 1) (hb : d67670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53666, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3837 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53667 q = 1) (hb : d67671 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d67671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53667, d67671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53668 q = 1) (hb : d67672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d67672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53668, d67672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53669 q = 1) (hb : d67673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d67673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53669, d67673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53670 q = 1) (hb : d67674 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d67674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53670, d67674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53671 q = 1) (hb : d67675 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d67675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53671, d67675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3839 (p : Pattern) (ha : d53677 p = 1) (hb : d67681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d67641 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d67641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d67641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3833 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d67642 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d67642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d67642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d67643 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d67643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d67643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d67644 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d67644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d67644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d67645 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d67645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d67645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53672 q = 1) (hb : d67676 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d67676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d67676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3838 q ha hb
  have h8 (q : Pattern) (ha : d53673 q = 1) (hb : d67677 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d67677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d67677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53674 q = 1) (hb : d67678 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d67678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d67678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53675 q = 1) (hb : d67679 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d67679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d67679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53676 q = 1) (hb : d67680 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d67680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d67680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53677 q = 1) (hb : d67681 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d67681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53677, d67681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3840 (p : Pattern) (ha : d497 p = 1) (hb : d67685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d493 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d67682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d494, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d67683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d495, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d67684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d496, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d497 q = 1) (hb : d67685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d67685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d67685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3841 (p : Pattern) (ha : d507 p = 1) (hb : d67689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d67682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d67683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d67684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d614 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d503 q = 1) (hb : d4413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d4413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d503, d4413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d504 q = 1) (hb : d67686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d504, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d505 q = 1) (hb : d67687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d67687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d505, d67687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d506 q = 1) (hb : d67688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d67688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d506, d67688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d507 q = 1) (hb : d67689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d67689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d507, d67689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3842 (p : Pattern) (ha : d53680 p = 1) (hb : d67696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d4413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d4413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d4413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d504 q = 1) (hb : d67686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d505 q = 1) (hb : d67694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d506 q = 1) (hb : d67695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53680 q = 1) (hb : d67696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3843 (p : Pattern) (ha : d53691 p = 1) (hb : d67705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4428 q = 1) (hb : d53687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4428, d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53688 q = 1) (hb : d67702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d67702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53688, d67702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53689 q = 1) (hb : d67703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53690 q = 1) (hb : d67704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53691 q = 1) (hb : d67705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3844 (p : Pattern) (ha : d53697 p = 1) (hb : d67711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d67690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d67690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3840 q ha hb
    | true =>
      simp only [d508, d67690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3841 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d67691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d67691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d67691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53678 q = 1) (hb : d67692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d67692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, d67692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d67693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d67693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d67693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53681 q = 1) (hb : d67697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53681, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3842 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53682 q = 1) (hb : d67698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d67698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53682, d67698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53683 q = 1) (hb : d67699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d67699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53683, d67699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53684 q = 1) (hb : d67700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d67700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53684, d67700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53685 q = 1) (hb : d67701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d67701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53685, d67701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53692 q = 1) (hb : d67706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53692, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3843 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53693 q = 1) (hb : d67707 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d67707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53693, d67707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53694 q = 1) (hb : d67708 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d67708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53694, d67708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53695 q = 1) (hb : d67709 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d67709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53695, d67709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53696 q = 1) (hb : d67710 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d67710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53696, d67710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53697 q = 1) (hb : d67711 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d67711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53697, d67711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3845 (p : Pattern) (ha : d53703 p = 1) (hb : d67717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d67712 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d67712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d67712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3844 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d67713 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d67713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d67713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d67714 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d67714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d67714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d67715 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d67715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d67715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d67716 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d67716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d67716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d67717 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d67717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d67717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3846 (p : Pattern) (ha : d789 p = 1) (hb : d67722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d785 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d67719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d786, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d67720 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d787, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d67721 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d788, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d789 q = 1) (hb : d67722 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d67722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d67722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3847 (p : Pattern) (ha : d799 p = 1) (hb : d67726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d67719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d67720 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d67721 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d795 q = 1) (hb : d4451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d4451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d795, d4451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d796 q = 1) (hb : d67723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d796, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d797 q = 1) (hb : d67724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d67724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d797, d67724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d798 q = 1) (hb : d67725 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d67725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d798, d67725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d799 q = 1) (hb : d67726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d67726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d799, d67726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3848 (p : Pattern) (ha : d53707 p = 1) (hb : d67733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d4451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d4451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d4451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d796 q = 1) (hb : d67723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d797 q = 1) (hb : d67731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d798 q = 1) (hb : d67732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53707 q = 1) (hb : d67733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3849 (p : Pattern) (ha : d53718 p = 1) (hb : d67742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1012 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4466 q = 1) (hb : d53714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4466, d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53715 q = 1) (hb : d67739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53715, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53716 q = 1) (hb : d67740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53717 q = 1) (hb : d67741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53718 q = 1) (hb : d67742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3850 (p : Pattern) (ha : d53724 p = 1) (hb : d67748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d67727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d67727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3846 q ha hb
    | true =>
      simp only [d800, d67727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3847 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d67728 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d67728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d67728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53705 q = 1) (hb : d67729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d67729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, d67729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d67730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d67730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d67730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53708 q = 1) (hb : d67734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53708, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3848 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53709 q = 1) (hb : d67735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d67735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53709, d67735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53710 q = 1) (hb : d67736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d67736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53710, d67736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53711 q = 1) (hb : d67737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d67737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53711, d67737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53712 q = 1) (hb : d67738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d67738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53712, d67738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53719 q = 1) (hb : d67743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53719, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3849 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53720 q = 1) (hb : d67744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d67744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53720, d67744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53721 q = 1) (hb : d67745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d67745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53721, d67745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53722 q = 1) (hb : d67746 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d67746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53722, d67746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53723 q = 1) (hb : d67747 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d67747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53723, d67747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53724 q = 1) (hb : d67748 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d67748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53724, d67748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3851 (p : Pattern) (ha : d53730 p = 1) (hb : d67754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d67749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d67749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d67749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3850 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d67750 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d67750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d67750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d67751 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d67751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d67751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d67752 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d67752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d67752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d67753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d67753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d67753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d67754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d67754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d67754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3852 (p : Pattern) (ha : d1168 p = 1) (hb : d67760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1164 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1165, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d67758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1166, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d67759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1167, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1168 q = 1) (hb : d67760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d67760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d67760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3853 (p : Pattern) (ha : d1178 p = 1) (hb : d67764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d67758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d67759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1174 q = 1) (hb : d4490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d4490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1174, d4490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d1175 q = 1) (hb : d67761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1175, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d1176 q = 1) (hb : d67762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d67762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1176, d67762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1177 q = 1) (hb : d67763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d67763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1177, d67763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1178 q = 1) (hb : d67764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d67764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1178, d67764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3854 (p : Pattern) (ha : d53735 p = 1) (hb : d67771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d4490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d4490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d4490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1175 q = 1) (hb : d67761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1176 q = 1) (hb : d67769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1177 q = 1) (hb : d67770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53735 q = 1) (hb : d67771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3855 (p : Pattern) (ha : d53746 p = 1) (hb : d67780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d53742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4505, d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53743 q = 1) (hb : d67777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53743, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53744 q = 1) (hb : d67778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53745 q = 1) (hb : d67779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53746 q = 1) (hb : d67780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3856 (p : Pattern) (ha : d53752 p = 1) (hb : d67786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d67765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d67765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3852 q ha hb
    | true =>
      simp only [d1179, d67765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3853 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d67766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d67766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d67766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53733 q = 1) (hb : d67767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d67767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, d67767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d67768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d67768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d67768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53736 q = 1) (hb : d67772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53736, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3854 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53737 q = 1) (hb : d67773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d67773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53737, d67773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53738 q = 1) (hb : d67774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d67774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53738, d67774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53739 q = 1) (hb : d67775 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d67775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53739, d67775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53740 q = 1) (hb : d67776 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d67776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53740, d67776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53747 q = 1) (hb : d67781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53747, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3855 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53748 q = 1) (hb : d67782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d67782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53748, d67782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53749 q = 1) (hb : d67783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d67783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53749, d67783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53750 q = 1) (hb : d67784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d67784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53750, d67784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53751 q = 1) (hb : d67785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d67785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53751, d67785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53752 q = 1) (hb : d67786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d67786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53752, d67786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3857 (p : Pattern) (ha : d53758 p = 1) (hb : d67792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d67787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d67787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d67787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3856 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d67788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d67788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d67788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d67789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d67789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d67789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d67790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d67790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d67790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d67791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d67791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d67791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d67792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d67792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d67792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3858 (p : Pattern) (ha : d1629 p = 1) (hb : d67799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1625 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1626, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d67797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1627, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d67798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1628, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1629 q = 1) (hb : d67799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d67799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d67799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3859 (p : Pattern) (ha : d1639 p = 1) (hb : d67803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d67797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d67798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1635 q = 1) (hb : d4530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d4530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1635, d4530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d1636 q = 1) (hb : d67800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1636, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d1637 q = 1) (hb : d67801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d67801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1637, d67801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1638 q = 1) (hb : d67802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d67802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1638, d67802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1639 q = 1) (hb : d67803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d67803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1639, d67803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3860 (p : Pattern) (ha : d53764 p = 1) (hb : d67810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d4530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d4530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d4530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1636 q = 1) (hb : d67800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1637 q = 1) (hb : d67808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1638 q = 1) (hb : d67809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53764 q = 1) (hb : d67810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3861 (p : Pattern) (ha : d53775 p = 1) (hb : d67819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d53771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4545, d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53772 q = 1) (hb : d67816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53772, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53773 q = 1) (hb : d67817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53774 q = 1) (hb : d67818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53775 q = 1) (hb : d67819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3862 (p : Pattern) (ha : d53781 p = 1) (hb : d67825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d67804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d67804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3858 q ha hb
    | true =>
      simp only [d1640, d67804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3859 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d67805 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d67805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d67805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d67806 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d67806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, d67806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d67807 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d67807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d67807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53765 q = 1) (hb : d67811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53765, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3860 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53766 q = 1) (hb : d67812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d67812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53766, d67812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53767 q = 1) (hb : d67813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d67813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53767, d67813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53768 q = 1) (hb : d67814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d67814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53768, d67814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53769 q = 1) (hb : d67815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d67815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53769, d67815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53776 q = 1) (hb : d67820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53776, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3861 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53777 q = 1) (hb : d67821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d67821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53777, d67821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53778 q = 1) (hb : d67822 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d67822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53778, d67822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53779 q = 1) (hb : d67823 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d67823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53779, d67823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53780 q = 1) (hb : d67824 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d67824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53780, d67824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53781 q = 1) (hb : d67825 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d67825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53781, d67825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3863 (p : Pattern) (ha : d53787 p = 1) (hb : d67831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d67826 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d67826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d67826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3862 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d67827 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d67827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d67827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d67828 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d67828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d67828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d67829 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d67829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d67829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d67830 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d67830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d67830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d67831 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d67831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d67831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3864 (p : Pattern) (ha : d2112 p = 1) (hb : d67839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2108 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2109, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d67837 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2110, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d67838 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2111, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2112 q = 1) (hb : d67839 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d67839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d67839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro3865 (p : Pattern) (ha : d2122 p = 1) (hb : d67843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d67837 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d67838 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2118 q = 1) (hb : d4571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d4571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2118, d4571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d2119 q = 1) (hb : d67840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2119, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d2120 q = 1) (hb : d67841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d67841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2120, d67841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2121 q = 1) (hb : d67842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d67842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2121, d67842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2122 q = 1) (hb : d67843 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d67843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2122, d67843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro3866 (p : Pattern) (ha : d53794 p = 1) (hb : d67850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2118 q = 1) (hb : d4571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d4571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d4571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2119 q = 1) (hb : d67840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2119, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2120 q = 1) (hb : d67848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2121 q = 1) (hb : d67849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53794 q = 1) (hb : d67850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3867 (p : Pattern) (ha : d53805 p = 1) (hb : d67859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d53801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4586, d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53802 q = 1) (hb : d67856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53802, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53803 q = 1) (hb : d67857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53804 q = 1) (hb : d67858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53805 q = 1) (hb : d67859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3868 (p : Pattern) (ha : d53811 p = 1) (hb : d67865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d67844 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d67844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3864 q ha hb
    | true =>
      simp only [d2123, d67844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3865 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d67845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d67845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d67845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d67846 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d67846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, d67846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d67847 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d67847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d67847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53795 q = 1) (hb : d67851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53795, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3866 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53796 q = 1) (hb : d67852 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d67852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53796, d67852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53797 q = 1) (hb : d67853 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d67853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53797, d67853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53798 q = 1) (hb : d67854 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d67854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53798, d67854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53799 q = 1) (hb : d67855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d67855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53799, d67855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53806 q = 1) (hb : d67860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53806, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3867 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53807 q = 1) (hb : d67861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d67861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53807, d67861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53808 q = 1) (hb : d67862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d67862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53808, d67862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53809 q = 1) (hb : d67863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d67863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53809, d67863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53810 q = 1) (hb : d67864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d67864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53810, d67864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d53811 q = 1) (hb : d67865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d67865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53811, d67865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro3869 (p : Pattern) (ha : d53817 p = 1) (hb : d67871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d67866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d67866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d67866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3868 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d67867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d67867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d67867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d67868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d67868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d67868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d67869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d67869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d67869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d67870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d67870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d67870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d67871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d67871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d67871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3870 (p : Pattern) (ha : d53823 p = 1) (hb : d67877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d67718 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d67718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3839 q ha hb
    | true =>
      simp only [d53704, d67718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3845 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d67755 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d67755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d67755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3851 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d67756 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d67756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d67756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d67793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d67793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d67793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3857 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d67794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d67794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d67794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d67795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d67795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d67795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d67832 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d67832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d67832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3863 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d67833 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d67833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d67833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d67834 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d67834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d67834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d67835 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d67835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d67835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d67872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d67872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d67872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3869 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d67873 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d67873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d67873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d67874 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d67874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d67874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d67875 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d67875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d67875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d67876 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d67876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d67876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d67877 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d67877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d67877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3871 (p : Pattern) (ha : d53829 p = 1) (hb : d67883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d67878 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d67878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3870 q ha hb
    | true =>
      simp only [d53824, d67878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d67879 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d67879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d67879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d67880 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d67880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d67880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d67881 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d67881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d67881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d67882 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d67882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d67882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d67883 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d67883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d67883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3872 (p : Pattern) (ha : d53835 p = 1) (hb : d67889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d67884 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d67884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3871 q ha hb
    | true =>
      simp only [d53830, d67884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d67885 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d67885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d67885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d67886 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d67886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d67886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d67887 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d67887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d67887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d67888 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d67888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d67888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d67889 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d67889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d67889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3873 (p : Pattern) (ha : d53841 p = 1) (hb : d67895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d67890 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d67890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3872 q ha hb
    | true =>
      simp only [d53836, d67890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d67891 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d67891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d67891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d67892 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d67892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d67892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d67893 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d67893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d67893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d67894 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d67894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d67894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d67895 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d67895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d67895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3874 (p : Pattern) (ha : d53847 p = 1) (hb : d67901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d67896 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d67896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3873 q ha hb
    | true =>
      simp only [d53842, d67896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d67897 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d67897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d67897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d67898 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d67898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d67898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d67899 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d67899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d67899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d67900 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d67900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d67900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d67901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d67901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d67901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3875 (p : Pattern) (ha : d53853 p = 1) (hb : d67907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d67902 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d67902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3874 q ha hb
    | true =>
      simp only [d53848, d67902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d67903 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d67903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d67903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d67904 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d67904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d67904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d67905 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d67905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d67905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d67906 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d67906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d67906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d67907 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d67907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d67907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3876 (p : Pattern) (ha : d53859 p = 1) (hb : d67913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d67908 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d67908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3875 q ha hb
    | true =>
      simp only [d53854, d67908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d67909 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d67909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d67909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d67910 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d67910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d67910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d67911 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d67911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d67911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d67912 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d67912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d67912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d67913 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d67913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d67913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3877 (p : Pattern) (ha : d53865 p = 1) (hb : d67919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d67914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d67914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3876 q ha hb
    | true =>
      simp only [d53860, d67914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d67915 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d67915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d67915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d67916 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d67916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d67916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d67917 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d67917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d67917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d67918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d67918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d67918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d67919 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d67919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d67919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3878 (p : Pattern) (ha : d48 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d45, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3879 (p : Pattern) (ha : d55 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d45, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3880 (p : Pattern) (ha : d60 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3881 (p : Pattern) (ha : d89 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d86, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3882 (p : Pattern) (ha : d95 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3878 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3879 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3880 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3881 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3883 (p : Pattern) (ha : d104 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3884 (p : Pattern) (ha : d111 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d108, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d109 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d110 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d111 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3885 (p : Pattern) (ha : d213 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3886 (p : Pattern) (ha : d4349 p = 1) (hb : d57572 p = 1) : d67937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4340 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d51 q = 1) : d51 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4341 q = 1) (hb : d57572 q = 1) : d67929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d57572, d67929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4341, d57572, d67929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4342 q = 1) (hb : d57572 q = 1) : d67930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d67930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d67930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4343 q = 1) (hb : d57572 q = 1) : d67931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d67931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d67931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4349 q = 1) (hb : d57572 q = 1) : d67937 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d67937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d67937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3887 (p : Pattern) (ha : d4359 p = 1) (hb : d57572 p = 1) : d67946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d85 q = 1) : d85 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4356 q = 1) (hb : d57572 q = 1) : d67943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d57572, d67943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4356, d57572, d67943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4357 q = 1) (hb : d57572 q = 1) : d67944 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d67944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d67944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4358 q = 1) (hb : d57572 q = 1) : d67945 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d67945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d67945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4359 q = 1) (hb : d57572 q = 1) : d67946 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d67946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d67946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3888 (p : Pattern) (ha : d51643 p = 1) (hb : d57572 p = 1) : d67928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d125 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d126 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d126, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d44 q = 1) : d44 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4336 q = 1) (hb : d57572 q = 1) : d67925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d57572, d67925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4336, d57572, d67925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51641 q = 1) (hb : d57572 q = 1) : d67926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d67926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51641, d67926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51642 q = 1) (hb : d57572 q = 1) : d67927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d67927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d67927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51643 q = 1) (hb : d57572 q = 1) : d67928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d67928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d67928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3889 (p : Pattern) (ha : d51646 p = 1) (hb : d57572 p = 1) : d67932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d125 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d126 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d126, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d44 q = 1) : d44 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4336 q = 1) (hb : d57572 q = 1) : d67925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d57572, d67925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4336, d57572, d67925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51641 q = 1) (hb : d57572 q = 1) : d67926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d67926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51641, d67926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51642 q = 1) (hb : d57572 q = 1) : d67927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d67927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d67927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d196 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d197 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d197, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d198 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d201 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d202 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d202, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4340 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d51 q = 1) : d51 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4341 q = 1) (hb : d57572 q = 1) : d67929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d57572, d67929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4341, d57572, d67929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51644 q = 1) (hb : d57572 q = 1) : d67930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d67930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51644, d67930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51645 q = 1) (hb : d57572 q = 1) : d67931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d67931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51645, d67931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51646 q = 1) (hb : d57572 q = 1) : d67932 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d67932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51646, d67932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3890 (p : Pattern) (ha : d51652 p = 1) (hb : d57572 p = 1) : d67952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3883 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3883 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3884 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d57572 q = 1) : d67933 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d67933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3888 q ha hb
    | true =>
      simp only [d51647, d67933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3889 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3885 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d57572 q = 1) : d67934 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d67934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d67934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d57572 q = 1) : d67935 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d67935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d67935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d57572 q = 1) : d67936 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d67936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d67936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d57572 q = 1) : d67938 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d67938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d67938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3886 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d57572 q = 1) : d67939 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d67939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d67939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d57572 q = 1) : d67940 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d67940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d67940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d57572 q = 1) : d67941 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d67941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d67941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51651 q = 1) (hb : d57572 q = 1) : d67942 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d67942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51651, d67942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d57572 q = 1) : d67947 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d67947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d67947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3887 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d57572 q = 1) : d67948 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d67948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, d67948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d57572 q = 1) : d67949 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d67949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, d67949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d57572 q = 1) : d67950 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d67950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, d67950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d57572 q = 1) : d67951 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d67951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, d67951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51652 q = 1) (hb : d57572 q = 1) : d67952 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d67952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51652, d67952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro3891 (p : Pattern) (ha : d284 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3892 (p : Pattern) (ha : d291 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d287 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d288 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d289 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d291 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3893 (p : Pattern) (ha : d397 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d101, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d397 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3894 (p : Pattern) (ha : d406 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3895 (p : Pattern) (ha : d462 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d459, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3896 (p : Pattern) (ha : d4385 p = 1) (hb : d57572 p = 1) : d67970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4376 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d391 q = 1) : d391 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4377 q = 1) (hb : d57572 q = 1) : d67962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d57572, d67962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4377, d57572, d67962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4378 q = 1) (hb : d57572 q = 1) : d67963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d67963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d67963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4379 q = 1) (hb : d57572 q = 1) : d67964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d67964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d67964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4385 q = 1) (hb : d57572 q = 1) : d67970 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d67970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d67970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3897 (p : Pattern) (ha : d4395 p = 1) (hb : d57572 p = 1) : d67979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d452 q = 1) : d452 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4392 q = 1) (hb : d57572 q = 1) : d67976 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d57572, d67976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4392, d57572, d67976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4393 q = 1) (hb : d57572 q = 1) : d67977 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d67977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4393, d67977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4394 q = 1) (hb : d57572 q = 1) : d67978 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d67978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4394, d67978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4395 q = 1) (hb : d57572 q = 1) : d67979 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d67979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d67979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3898 (p : Pattern) (ha : d51660 p = 1) (hb : d57572 p = 1) : d67961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d305 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d371 q = 1) : d371 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4372 q = 1) (hb : d57572 q = 1) : d67958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d57572, d67958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4372, d57572, d67958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51658 q = 1) (hb : d57572 q = 1) : d67959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d67959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51658, d67959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51659 q = 1) (hb : d57572 q = 1) : d67960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d67960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51659, d67960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51660 q = 1) (hb : d57572 q = 1) : d67961 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d67961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d67961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3899 (p : Pattern) (ha : d51663 p = 1) (hb : d57572 p = 1) : d67965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d305 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d371 q = 1) : d371 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4372 q = 1) (hb : d57572 q = 1) : d67958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d57572, d67958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4372, d57572, d67958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51658 q = 1) (hb : d57572 q = 1) : d67959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d67959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51658, d67959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51659 q = 1) (hb : d57572 q = 1) : d67960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d67960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51659, d67960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d378 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d379 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d379, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d380 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d383 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d384 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d384, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4376 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d391 q = 1) : d391 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4377 q = 1) (hb : d57572 q = 1) : d67962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d57572, d67962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4377, d57572, d67962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51661 q = 1) (hb : d57572 q = 1) : d67963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d67963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51661, d67963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51662 q = 1) (hb : d57572 q = 1) : d67964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d67964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51662, d67964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51663 q = 1) (hb : d57572 q = 1) : d67965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d67965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51663, d67965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3900 (p : Pattern) (ha : d51676 p = 1) (hb : d57572 p = 1) : d67985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3891 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3891 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3892 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d57572 q = 1) : d67966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d67966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3898 q ha hb
    | true =>
      simp only [d51664, d67966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3899 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3893 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3884 q ha hb
  have h8 (q : Pattern) (ha : d51665 q = 1) (hb : d57572 q = 1) : d67967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d67967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51665, d67967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51666 q = 1) (hb : d57572 q = 1) : d67968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d67968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51666, d67968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51667 q = 1) (hb : d57572 q = 1) : d67969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d67969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51667, d67969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4386 q = 1) (hb : d57572 q = 1) : d67971 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d67971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d67971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3896 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3894 q ha hb
  have h13 (q : Pattern) (ha : d51668 q = 1) (hb : d57572 q = 1) : d67972 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, d67972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51668, d67972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51669 q = 1) (hb : d57572 q = 1) : d67973 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, d67973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51669, d67973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51670 q = 1) (hb : d57572 q = 1) : d67974 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, d67974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51670, d67974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51671 q = 1) (hb : d57572 q = 1) : d67975 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d67975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51671, d67975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4396 q = 1) (hb : d57572 q = 1) : d67980 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d67980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d67980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3897 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3895 q ha hb
  have h19 (q : Pattern) (ha : d51672 q = 1) (hb : d57572 q = 1) : d67981 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51672, d67981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51672, d67981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51673 q = 1) (hb : d57572 q = 1) : d67982 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51673, d67982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51673, d67982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51674 q = 1) (hb : d57572 q = 1) : d67983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51674, d67983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51674, d67983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51675 q = 1) (hb : d57572 q = 1) : d67984 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51675, d67984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51675, d67984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51676 q = 1) (hb : d57572 q = 1) : d67985 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51676, d67985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51676, d67985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3901 (p : Pattern) (ha : d51682 p = 1) (hb : d57572 p = 1) : d67991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3882 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d57572 q = 1) : d67953 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d67953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d67953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3890 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d57572 q = 1) : d67954 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d67954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d67954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d57572 q = 1) : d67955 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d67955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d67955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d57572 q = 1) : d67956 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d67956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d67956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d57572 q = 1) : d67957 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d67957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d67957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51677 q = 1) (hb : d57572 q = 1) : d67986 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51677, d67986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51677, d67986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3900 q ha hb
  have h11 (q : Pattern) (ha : d51678 q = 1) (hb : d57572 q = 1) : d67987 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51678, d67987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51678, d67987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51679 q = 1) (hb : d57572 q = 1) : d67988 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51679, d67988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51679, d67988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51680 q = 1) (hb : d57572 q = 1) : d67989 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51680, d67989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51680, d67989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51681 q = 1) (hb : d57572 q = 1) : d67990 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51681, d67990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51681, d67990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51682 q = 1) (hb : d57572 q = 1) : d67991 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51682, d67991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51682, d67991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3902 (p : Pattern) (ha : d497 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d494, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d497 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3903 (p : Pattern) (ha : d507 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d494, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d503 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d504 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d504, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d505 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d506 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d507 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3904 (p : Pattern) (ha : d638 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d494, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d634 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d635 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d635, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d636 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d637 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d638 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3905 (p : Pattern) (ha : d644 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d634 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d635, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d640 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d641 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d641, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d642 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d643 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d644 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3906 (p : Pattern) (ha : d653 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d640 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d641, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3907 (p : Pattern) (ha : d736 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d732 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d733, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3908 (p : Pattern) (ha : d4422 p = 1) (hb : d57572 p = 1) : d68004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4413 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d627 q = 1) : d627 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4414 q = 1) (hb : d57572 q = 1) : d67996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d57572, d67996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4414, d57572, d67996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4415 q = 1) (hb : d57572 q = 1) : d67997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d67997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d67997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4416 q = 1) (hb : d57572 q = 1) : d67998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d67998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d67998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4422 q = 1) (hb : d57572 q = 1) : d68004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d68004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d68004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3909 (p : Pattern) (ha : d4432 p = 1) (hb : d57572 p = 1) : d68013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d721 q = 1) : d721 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4429 q = 1) (hb : d57572 q = 1) : d68010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d57572, d68010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4429, d57572, d68010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4430 q = 1) (hb : d57572 q = 1) : d68011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d68011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4430, d68011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4431 q = 1) (hb : d57572 q = 1) : d68012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d68012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4431, d68012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4432 q = 1) (hb : d57572 q = 1) : d68013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d68013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d68013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3910 (p : Pattern) (ha : d51685 p = 1) (hb : d57572 p = 1) : d67995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d526 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d527 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d604 q = 1) : d604 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4409 q = 1) (hb : d57572 q = 1) : d67992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d57572, d67992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4409, d57572, d67992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51683 q = 1) (hb : d57572 q = 1) : d67993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d67993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51683, d67993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51684 q = 1) (hb : d57572 q = 1) : d67994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d67994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51684, d67994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51685 q = 1) (hb : d57572 q = 1) : d67995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d67995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d67995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3911 (p : Pattern) (ha : d51688 p = 1) (hb : d57572 p = 1) : d67999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d526 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d527 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d604 q = 1) : d604 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4409 q = 1) (hb : d57572 q = 1) : d67992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d57572, d67992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4409, d57572, d67992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51683 q = 1) (hb : d57572 q = 1) : d67993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d67993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51683, d67993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51684 q = 1) (hb : d57572 q = 1) : d67994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d67994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51684, d67994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d612 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d613 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d613, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d614 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d618 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d619 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d619, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4413 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d627 q = 1) : d627 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4414 q = 1) (hb : d57572 q = 1) : d67996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d57572, d67996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4414, d57572, d67996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51686 q = 1) (hb : d57572 q = 1) : d67997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d67997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51686, d67997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51687 q = 1) (hb : d57572 q = 1) : d67998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d67998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51687, d67998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51688 q = 1) (hb : d57572 q = 1) : d67999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d67999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51688, d67999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3912 (p : Pattern) (ha : d51701 p = 1) (hb : d57572 p = 1) : d68019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3902 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3902 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3903 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d57572 q = 1) : d68000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d68000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3910 q ha hb
    | true =>
      simp only [d51689, d68000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3911 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3904 q ha hb
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3905 q ha hb
  have h8 (q : Pattern) (ha : d51690 q = 1) (hb : d57572 q = 1) : d68001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d68001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51690, d68001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51691 q = 1) (hb : d57572 q = 1) : d68002 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d68002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51691, d68002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51692 q = 1) (hb : d57572 q = 1) : d68003 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d68003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51692, d68003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4423 q = 1) (hb : d57572 q = 1) : d68005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d68005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d68005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3908 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3906 q ha hb
  have h13 (q : Pattern) (ha : d51693 q = 1) (hb : d57572 q = 1) : d68006 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, d68006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51693, d68006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51694 q = 1) (hb : d57572 q = 1) : d68007 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, d68007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51694, d68007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51695 q = 1) (hb : d57572 q = 1) : d68008 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, d68008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51695, d68008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51696 q = 1) (hb : d57572 q = 1) : d68009 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d68009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51696, d68009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4433 q = 1) (hb : d57572 q = 1) : d68014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d68014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d68014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3909 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3907 q ha hb
  have h19 (q : Pattern) (ha : d51697 q = 1) (hb : d57572 q = 1) : d68015 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51697, d68015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51697, d68015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51698 q = 1) (hb : d57572 q = 1) : d68016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51698, d68016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51698, d68016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51699 q = 1) (hb : d57572 q = 1) : d68017 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51699, d68017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51699, d68017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51700 q = 1) (hb : d57572 q = 1) : d68018 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51700, d68018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51700, d68018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51701 q = 1) (hb : d57572 q = 1) : d68019 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51701, d68019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51701, d68019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3913 (p : Pattern) (ha : d51707 p = 1) (hb : d57572 p = 1) : d68025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51702 q = 1) (hb : d57572 q = 1) : d68020 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51702, d68020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51702, d68020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3912 q ha hb
  have h2 (q : Pattern) (ha : d51703 q = 1) (hb : d57572 q = 1) : d68021 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51703, d68021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51703, d68021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51704 q = 1) (hb : d57572 q = 1) : d68022 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51704, d68022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51704, d68022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51705 q = 1) (hb : d57572 q = 1) : d68023 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51705, d68023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51705, d68023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51706 q = 1) (hb : d57572 q = 1) : d68024 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51706, d68024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51706, d68024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51707 q = 1) (hb : d57572 q = 1) : d68025 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51707, d68025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51707, d68025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3914 (p : Pattern) (ha : d789 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d785 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d786, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d789 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3915 (p : Pattern) (ha : d799 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d785 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d786, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d795 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d796 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d796, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d797 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d798 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d799 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3916 (p : Pattern) (ha : d944 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d785 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d786, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d940 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d941 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d941, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d942 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d943 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d944 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3917 (p : Pattern) (ha : d950 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d940 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d941, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d946 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d947 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d947, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d948 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d949 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d950 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3918 (p : Pattern) (ha : d959 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d947, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3919 (p : Pattern) (ha : d1069 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1066, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3920 (p : Pattern) (ha : d4460 p = 1) (hb : d57572 p = 1) : d68039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d933 q = 1) : d933 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4452 q = 1) (hb : d57572 q = 1) : d68031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d57572, d68031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4452, d57572, d68031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4453 q = 1) (hb : d57572 q = 1) : d68032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d68032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d68032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4454 q = 1) (hb : d57572 q = 1) : d68033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d68033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d68033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4460 q = 1) (hb : d57572 q = 1) : d68039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d68039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d68039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3921 (p : Pattern) (ha : d4470 p = 1) (hb : d57572 p = 1) : d68048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1054 q = 1) : d1054 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4467 q = 1) (hb : d57572 q = 1) : d68045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d57572, d68045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4467, d57572, d68045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4468 q = 1) (hb : d57572 q = 1) : d68046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d68046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4468, d68046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4469 q = 1) (hb : d57572 q = 1) : d68047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d68047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4469, d68047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4470 q = 1) (hb : d57572 q = 1) : d68048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d68048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d68048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3922 (p : Pattern) (ha : d51711 p = 1) (hb : d57572 p = 1) : d68030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d818 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d819 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d910 q = 1) : d910 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4447 q = 1) (hb : d57572 q = 1) : d68027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d57572, d68027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4447, d57572, d68027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51709 q = 1) (hb : d57572 q = 1) : d68028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d68028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51709, d68028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51710 q = 1) (hb : d57572 q = 1) : d68029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d68029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51710, d68029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51711 q = 1) (hb : d57572 q = 1) : d68030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d68030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d68030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3923 (p : Pattern) (ha : d51714 p = 1) (hb : d57572 p = 1) : d68034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d818 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d819 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d910 q = 1) : d910 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4447 q = 1) (hb : d57572 q = 1) : d68027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d57572, d68027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4447, d57572, d68027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51709 q = 1) (hb : d57572 q = 1) : d68028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d68028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51709, d68028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51710 q = 1) (hb : d57572 q = 1) : d68029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d68029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51710, d68029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d918 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d919 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d919, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d920 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d924 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d925 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d925, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4451 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d933 q = 1) : d933 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4452 q = 1) (hb : d57572 q = 1) : d68031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d57572, d68031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4452, d57572, d68031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51712 q = 1) (hb : d57572 q = 1) : d68032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d68032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51712, d68032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51713 q = 1) (hb : d57572 q = 1) : d68033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d68033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51713, d68033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51714 q = 1) (hb : d57572 q = 1) : d68034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d68034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51714, d68034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3924 (p : Pattern) (ha : d51727 p = 1) (hb : d57572 p = 1) : d68054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3914 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3914 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3915 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d57572 q = 1) : d68035 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d68035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3922 q ha hb
    | true =>
      simp only [d51715, d68035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3923 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3916 q ha hb
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3917 q ha hb
  have h8 (q : Pattern) (ha : d51716 q = 1) (hb : d57572 q = 1) : d68036 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d68036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51716, d68036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51717 q = 1) (hb : d57572 q = 1) : d68037 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d68037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51717, d68037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51718 q = 1) (hb : d57572 q = 1) : d68038 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d68038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51718, d68038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4461 q = 1) (hb : d57572 q = 1) : d68040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d68040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d68040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3920 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3918 q ha hb
  have h13 (q : Pattern) (ha : d51719 q = 1) (hb : d57572 q = 1) : d68041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, d68041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51719, d68041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51720 q = 1) (hb : d57572 q = 1) : d68042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, d68042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51720, d68042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51721 q = 1) (hb : d57572 q = 1) : d68043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, d68043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51721, d68043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51722 q = 1) (hb : d57572 q = 1) : d68044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d68044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51722, d68044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4471 q = 1) (hb : d57572 q = 1) : d68049 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d68049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d68049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3921 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3919 q ha hb
  have h19 (q : Pattern) (ha : d51723 q = 1) (hb : d57572 q = 1) : d68050 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51723, d68050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51723, d68050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51724 q = 1) (hb : d57572 q = 1) : d68051 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51724, d68051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51724, d68051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51725 q = 1) (hb : d57572 q = 1) : d68052 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51725, d68052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51725, d68052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51726 q = 1) (hb : d57572 q = 1) : d68053 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51726, d68053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51726, d68053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51727 q = 1) (hb : d57572 q = 1) : d68054 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51727, d68054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51727, d68054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3925 (p : Pattern) (ha : d51733 p = 1) (hb : d57572 p = 1) : d68060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51728 q = 1) (hb : d57572 q = 1) : d68055 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51728, d68055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51728, d68055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3924 q ha hb
  have h2 (q : Pattern) (ha : d51729 q = 1) (hb : d57572 q = 1) : d68056 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51729, d68056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51729, d68056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51730 q = 1) (hb : d57572 q = 1) : d68057 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51730, d68057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51730, d68057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51731 q = 1) (hb : d57572 q = 1) : d68058 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51731, d68058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51731, d68058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51732 q = 1) (hb : d57572 q = 1) : d68059 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51732, d68059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51732, d68059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51733 q = 1) (hb : d57572 q = 1) : d68060 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51733, d68060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51733, d68060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3926 (p : Pattern) (ha : d1168 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1165, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1168 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3927 (p : Pattern) (ha : d1178 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1165, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1174 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1175 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1175, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1176 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1177 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1178 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3928 (p : Pattern) (ha : d1355 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1165, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1351 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1352 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1352, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1353 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1354 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1355 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3929 (p : Pattern) (ha : d1361 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1352, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1357 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1358 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1358, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1359 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1360 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1361 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3930 (p : Pattern) (ha : d1370 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1357 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1358, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3931 (p : Pattern) (ha : d1503 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1500, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3932 (p : Pattern) (ha : d4499 p = 1) (hb : d57572 p = 1) : d68075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4490 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1344 q = 1) : d1344 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4491 q = 1) (hb : d57572 q = 1) : d68067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d57572, d68067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4491, d57572, d68067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4492 q = 1) (hb : d57572 q = 1) : d68068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d68068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d68068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4493 q = 1) (hb : d57572 q = 1) : d68069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d68069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d68069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4499 q = 1) (hb : d57572 q = 1) : d68075 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d68075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d68075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3933 (p : Pattern) (ha : d4509 p = 1) (hb : d57572 p = 1) : d68084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1488 q = 1) : d1488 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4506 q = 1) (hb : d57572 q = 1) : d68081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d57572, d68081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4506, d57572, d68081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4507 q = 1) (hb : d57572 q = 1) : d68082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d68082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d68082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4508 q = 1) (hb : d57572 q = 1) : d68083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d68083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d68083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4509 q = 1) (hb : d57572 q = 1) : d68084 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d68084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d68084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3934 (p : Pattern) (ha : d51738 p = 1) (hb : d57572 p = 1) : d68066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1198 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1321 q = 1) : d1321 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4486 q = 1) (hb : d57572 q = 1) : d68063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d57572, d68063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4486, d57572, d68063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51736 q = 1) (hb : d57572 q = 1) : d68064 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d68064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51736, d68064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51737 q = 1) (hb : d57572 q = 1) : d68065 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d68065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51737, d68065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51738 q = 1) (hb : d57572 q = 1) : d68066 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d68066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d68066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3935 (p : Pattern) (ha : d51741 p = 1) (hb : d57572 p = 1) : d68070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1198 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1321 q = 1) : d1321 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4486 q = 1) (hb : d57572 q = 1) : d68063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d57572, d68063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4486, d57572, d68063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51736 q = 1) (hb : d57572 q = 1) : d68064 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d68064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51736, d68064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51737 q = 1) (hb : d57572 q = 1) : d68065 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d68065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51737, d68065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1329 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1330 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1330, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d1331 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1335 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1336 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1336, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4490 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d1344 q = 1) : d1344 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4491 q = 1) (hb : d57572 q = 1) : d68067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d57572, d68067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4491, d57572, d68067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51739 q = 1) (hb : d57572 q = 1) : d68068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d68068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51739, d68068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51740 q = 1) (hb : d57572 q = 1) : d68069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d68069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51740, d68069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51741 q = 1) (hb : d57572 q = 1) : d68070 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d68070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51741, d68070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3936 (p : Pattern) (ha : d51754 p = 1) (hb : d57572 p = 1) : d68090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3926 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3926 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3927 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d57572 q = 1) : d68071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d68071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3934 q ha hb
    | true =>
      simp only [d51742, d68071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3935 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3928 q ha hb
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3929 q ha hb
  have h8 (q : Pattern) (ha : d51743 q = 1) (hb : d57572 q = 1) : d68072 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d68072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51743, d68072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51744 q = 1) (hb : d57572 q = 1) : d68073 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d68073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51744, d68073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51745 q = 1) (hb : d57572 q = 1) : d68074 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d68074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51745, d68074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4500 q = 1) (hb : d57572 q = 1) : d68076 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d68076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d68076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3932 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3930 q ha hb
  have h13 (q : Pattern) (ha : d51746 q = 1) (hb : d57572 q = 1) : d68077 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, d68077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51746, d68077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51747 q = 1) (hb : d57572 q = 1) : d68078 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, d68078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51747, d68078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51748 q = 1) (hb : d57572 q = 1) : d68079 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, d68079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51748, d68079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51749 q = 1) (hb : d57572 q = 1) : d68080 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d68080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51749, d68080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4510 q = 1) (hb : d57572 q = 1) : d68085 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d68085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d68085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3933 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3931 q ha hb
  have h19 (q : Pattern) (ha : d51750 q = 1) (hb : d57572 q = 1) : d68086 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51750, d68086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51750, d68086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51751 q = 1) (hb : d57572 q = 1) : d68087 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51751, d68087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51751, d68087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51752 q = 1) (hb : d57572 q = 1) : d68088 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51752, d68088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51752, d68088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51753 q = 1) (hb : d57572 q = 1) : d68089 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51753, d68089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51753, d68089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51754 q = 1) (hb : d57572 q = 1) : d68090 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51754, d68090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51754, d68090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3937 (p : Pattern) (ha : d51760 p = 1) (hb : d57572 p = 1) : d68096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51755 q = 1) (hb : d57572 q = 1) : d68091 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51755, d68091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51755, d68091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3936 q ha hb
  have h2 (q : Pattern) (ha : d51756 q = 1) (hb : d57572 q = 1) : d68092 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51756, d68092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51756, d68092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51757 q = 1) (hb : d57572 q = 1) : d68093 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51757, d68093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51757, d68093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51758 q = 1) (hb : d57572 q = 1) : d68094 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51758, d68094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51758, d68094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51759 q = 1) (hb : d57572 q = 1) : d68095 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51759, d68095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51759, d68095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51760 q = 1) (hb : d57572 q = 1) : d68096 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51760, d68096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51760, d68096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3938 (p : Pattern) (ha : d1629 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1625 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1626, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1629 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3939 (p : Pattern) (ha : d1639 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1625 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1626, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1635 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1636 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1636, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1637 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1638 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1639 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3940 (p : Pattern) (ha : d1832 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1625 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1626, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1828 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1829 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1829, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1830 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1831 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1832 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3941 (p : Pattern) (ha : d1838 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1828 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1829, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1834 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1835 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1835, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1836 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1837 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1838 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3942 (p : Pattern) (ha : d1847 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1835, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3943 (p : Pattern) (ha : d1980 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1976 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1977, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3944 (p : Pattern) (ha : d4539 p = 1) (hb : d57572 p = 1) : d68112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1821 q = 1) : d1821 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4531 q = 1) (hb : d57572 q = 1) : d68104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d57572, d68104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4531, d57572, d68104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4532 q = 1) (hb : d57572 q = 1) : d68105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d68105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d68105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4533 q = 1) (hb : d57572 q = 1) : d68106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d68106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d68106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4539 q = 1) (hb : d57572 q = 1) : d68112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d68112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d68112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3945 (p : Pattern) (ha : d4549 p = 1) (hb : d57572 p = 1) : d68121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1965 q = 1) : d1965 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4546 q = 1) (hb : d57572 q = 1) : d68118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d57572, d68118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4546, d57572, d68118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4547 q = 1) (hb : d57572 q = 1) : d68119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d68119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d68119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4548 q = 1) (hb : d57572 q = 1) : d68120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d68120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d68120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4549 q = 1) (hb : d57572 q = 1) : d68121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d68121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d68121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3946 (p : Pattern) (ha : d51766 p = 1) (hb : d57572 p = 1) : d68103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1659 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1798 q = 1) : d1798 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4526 q = 1) (hb : d57572 q = 1) : d68100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d57572, d68100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4526, d57572, d68100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51764 q = 1) (hb : d57572 q = 1) : d68101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d68101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51764, d68101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51765 q = 1) (hb : d57572 q = 1) : d68102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d68102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51765, d68102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51766 q = 1) (hb : d57572 q = 1) : d68103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d68103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d68103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3947 (p : Pattern) (ha : d51769 p = 1) (hb : d57572 p = 1) : d68107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1659 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1798 q = 1) : d1798 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4526 q = 1) (hb : d57572 q = 1) : d68100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d57572, d68100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4526, d57572, d68100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51764 q = 1) (hb : d57572 q = 1) : d68101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d68101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51764, d68101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51765 q = 1) (hb : d57572 q = 1) : d68102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d68102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51765, d68102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1806 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1807 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1807, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d1808 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1812 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1813 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1813, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4530 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d1821 q = 1) : d1821 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4531 q = 1) (hb : d57572 q = 1) : d68104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d57572, d68104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4531, d57572, d68104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51767 q = 1) (hb : d57572 q = 1) : d68105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d68105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51767, d68105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51768 q = 1) (hb : d57572 q = 1) : d68106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d68106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51768, d68106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51769 q = 1) (hb : d57572 q = 1) : d68107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d68107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51769, d68107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3948 (p : Pattern) (ha : d51782 p = 1) (hb : d57572 p = 1) : d68127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3938 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3938 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3939 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d57572 q = 1) : d68108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d68108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3946 q ha hb
    | true =>
      simp only [d51770, d68108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3947 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3940 q ha hb
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3941 q ha hb
  have h8 (q : Pattern) (ha : d51771 q = 1) (hb : d57572 q = 1) : d68109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d68109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51771, d68109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51772 q = 1) (hb : d57572 q = 1) : d68110 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d68110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51772, d68110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51773 q = 1) (hb : d57572 q = 1) : d68111 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d68111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51773, d68111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4540 q = 1) (hb : d57572 q = 1) : d68113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d68113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d68113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3944 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3942 q ha hb
  have h13 (q : Pattern) (ha : d51774 q = 1) (hb : d57572 q = 1) : d68114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, d68114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51774, d68114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51775 q = 1) (hb : d57572 q = 1) : d68115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, d68115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51775, d68115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51776 q = 1) (hb : d57572 q = 1) : d68116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, d68116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51776, d68116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51777 q = 1) (hb : d57572 q = 1) : d68117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d68117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51777, d68117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4550 q = 1) (hb : d57572 q = 1) : d68122 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d68122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d68122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3945 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3943 q ha hb
  have h19 (q : Pattern) (ha : d51778 q = 1) (hb : d57572 q = 1) : d68123 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51778, d68123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51778, d68123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51779 q = 1) (hb : d57572 q = 1) : d68124 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51779, d68124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51779, d68124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51780 q = 1) (hb : d57572 q = 1) : d68125 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51780, d68125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51780, d68125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51781 q = 1) (hb : d57572 q = 1) : d68126 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51781, d68126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51781, d68126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51782 q = 1) (hb : d57572 q = 1) : d68127 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51782, d68127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51782, d68127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3949 (p : Pattern) (ha : d51788 p = 1) (hb : d57572 p = 1) : d68133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51783 q = 1) (hb : d57572 q = 1) : d68128 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51783, d68128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51783, d68128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3948 q ha hb
  have h2 (q : Pattern) (ha : d51784 q = 1) (hb : d57572 q = 1) : d68129 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51784, d68129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51784, d68129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51785 q = 1) (hb : d57572 q = 1) : d68130 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51785, d68130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51785, d68130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51786 q = 1) (hb : d57572 q = 1) : d68131 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51786, d68131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51786, d68131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51787 q = 1) (hb : d57572 q = 1) : d68132 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51787, d68132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51787, d68132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51788 q = 1) (hb : d57572 q = 1) : d68133 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51788, d68133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51788, d68133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3950 (p : Pattern) (ha : d2112 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2109, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2112 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3951 (p : Pattern) (ha : d2122 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2109, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2118 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2119 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d2120 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2121 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2122 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3952 (p : Pattern) (ha : d2310 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2109, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2307 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2307, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d2308 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2309 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2310 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3953 (p : Pattern) (ha : d2316 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2307, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2312 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2313 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2313, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d2314 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2315 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2316 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3954 (p : Pattern) (ha : d2325 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2313, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3955 (p : Pattern) (ha : d2458 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2455, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3956 (p : Pattern) (ha : d4580 p = 1) (hb : d57572 p = 1) : d68150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2299 q = 1) : d2299 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4572 q = 1) (hb : d57572 q = 1) : d68142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d57572, d68142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4572, d57572, d68142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4573 q = 1) (hb : d57572 q = 1) : d68143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d68143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d68143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4574 q = 1) (hb : d57572 q = 1) : d68144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d68144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d68144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4580 q = 1) (hb : d57572 q = 1) : d68150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d68150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d68150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3957 (p : Pattern) (ha : d4590 p = 1) (hb : d57572 p = 1) : d68159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4586 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2443 q = 1) : d2443 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d4587 q = 1) (hb : d57572 q = 1) : d68156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d57572, d68156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4587, d57572, d68156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4588 q = 1) (hb : d57572 q = 1) : d68157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d68157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d68157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4589 q = 1) (hb : d57572 q = 1) : d68158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d68158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d68158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4590 q = 1) (hb : d57572 q = 1) : d68159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d68159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d68159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3958 (p : Pattern) (ha : d51795 p = 1) (hb : d57572 p = 1) : d68141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2142 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d2276 q = 1) : d2276 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4567 q = 1) (hb : d57572 q = 1) : d68138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d57572, d68138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4567, d57572, d68138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51793 q = 1) (hb : d57572 q = 1) : d68139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d68139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51793, d68139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51794 q = 1) (hb : d57572 q = 1) : d68140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d68140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, d68140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51795 q = 1) (hb : d57572 q = 1) : d68141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d68141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d68141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3959 (p : Pattern) (ha : d51798 p = 1) (hb : d57572 p = 1) : d68145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2142 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d2276 q = 1) : d2276 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d4567 q = 1) (hb : d57572 q = 1) : d68138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d57572, d68138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4567, d57572, d68138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51793 q = 1) (hb : d57572 q = 1) : d68139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d68139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51793, d68139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51794 q = 1) (hb : d57572 q = 1) : d68140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d68140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, d68140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d2284 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2285 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2285, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d2286 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d2290 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d2291 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d2291, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4571 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d2299 q = 1) : d2299 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d4572 q = 1) (hb : d57572 q = 1) : d68142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d57572, d68142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d4572, d57572, d68142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d51796 q = 1) (hb : d57572 q = 1) : d68143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d68143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51796, d68143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51797 q = 1) (hb : d57572 q = 1) : d68144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d68144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51797, d68144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51798 q = 1) (hb : d57572 q = 1) : d68145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d68145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51798, d68145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro3960 (p : Pattern) (ha : d51811 p = 1) (hb : d57572 p = 1) : d68165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3950 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3950 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3951 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d57572 q = 1) : d68146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d68146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3958 q ha hb
    | true =>
      simp only [d51799, d68146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3959 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3952 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3953 q ha hb
  have h8 (q : Pattern) (ha : d51800 q = 1) (hb : d57572 q = 1) : d68147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d68147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51800, d68147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51801 q = 1) (hb : d57572 q = 1) : d68148 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d68148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51801, d68148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51802 q = 1) (hb : d57572 q = 1) : d68149 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d68149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51802, d68149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4581 q = 1) (hb : d57572 q = 1) : d68151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d68151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d68151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3956 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3954 q ha hb
  have h13 (q : Pattern) (ha : d51803 q = 1) (hb : d57572 q = 1) : d68152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, d68152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51803, d68152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51804 q = 1) (hb : d57572 q = 1) : d68153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, d68153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51804, d68153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51805 q = 1) (hb : d57572 q = 1) : d68154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, d68154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51805, d68154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51806 q = 1) (hb : d57572 q = 1) : d68155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d68155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51806, d68155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4591 q = 1) (hb : d57572 q = 1) : d68160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d68160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d68160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3957 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3955 q ha hb
  have h19 (q : Pattern) (ha : d51807 q = 1) (hb : d57572 q = 1) : d68161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51807, d68161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51807, d68161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51808 q = 1) (hb : d57572 q = 1) : d68162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51808, d68162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51808, d68162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51809 q = 1) (hb : d57572 q = 1) : d68163 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51809, d68163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51809, d68163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51810 q = 1) (hb : d57572 q = 1) : d68164 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51810, d68164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51810, d68164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51811 q = 1) (hb : d57572 q = 1) : d68165 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51811, d68165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51811, d68165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro3961 (p : Pattern) (ha : d51817 p = 1) (hb : d57572 p = 1) : d68171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51812 q = 1) (hb : d57572 q = 1) : d68166 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51812, d68166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51812, d68166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3960 q ha hb
  have h2 (q : Pattern) (ha : d51813 q = 1) (hb : d57572 q = 1) : d68167 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51813, d68167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51813, d68167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51814 q = 1) (hb : d57572 q = 1) : d68168 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51814, d68168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51814, d68168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51815 q = 1) (hb : d57572 q = 1) : d68169 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51815, d68169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51815, d68169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51816 q = 1) (hb : d57572 q = 1) : d68170 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51816, d68170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51816, d68170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51817 q = 1) (hb : d57572 q = 1) : d68171 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51817, d68171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51817, d68171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3962 (p : Pattern) (ha : d51823 p = 1) (hb : d57572 p = 1) : d68177 p = 1 := by
  have h0 (q : Pattern) (ha : d51708 q = 1) (hb : d57572 q = 1) : d68026 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51708, d68026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3901 q ha hb
    | true =>
      simp only [d51708, d68026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3913 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51734 q = 1) (hb : d57572 q = 1) : d68061 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51734, d68061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51734, d68061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3925 q ha hb
  have h3 (q : Pattern) (ha : d51735 q = 1) (hb : d57572 q = 1) : d68062 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51735, d68062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51735, d68062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51761 q = 1) (hb : d57572 q = 1) : d68097 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51761, d68097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51761, d68097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3937 q ha hb
  have h5 (q : Pattern) (ha : d51762 q = 1) (hb : d57572 q = 1) : d68098 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51762, d68098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51762, d68098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51763 q = 1) (hb : d57572 q = 1) : d68099 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51763, d68099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51763, d68099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51789 q = 1) (hb : d57572 q = 1) : d68134 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51789, d68134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51789, d68134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3949 q ha hb
  have h8 (q : Pattern) (ha : d51790 q = 1) (hb : d57572 q = 1) : d68135 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51790, d68135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51790, d68135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51791 q = 1) (hb : d57572 q = 1) : d68136 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51791, d68136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51791, d68136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51792 q = 1) (hb : d57572 q = 1) : d68137 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51792, d68137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51792, d68137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51818 q = 1) (hb : d57572 q = 1) : d68172 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51818, d68172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51818, d68172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3961 q ha hb
  have h12 (q : Pattern) (ha : d51819 q = 1) (hb : d57572 q = 1) : d68173 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51819, d68173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51819, d68173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51820 q = 1) (hb : d57572 q = 1) : d68174 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51820, d68174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51820, d68174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51821 q = 1) (hb : d57572 q = 1) : d68175 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51821, d68175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51821, d68175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51822 q = 1) (hb : d57572 q = 1) : d68176 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d51822, d68176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51822, d68176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51823 q = 1) (hb : d57572 q = 1) : d68177 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d51823, d68177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51823, d68177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3963 (p : Pattern) (ha : d51829 p = 1) (hb : d57572 p = 1) : d68183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51824 q = 1) (hb : d57572 q = 1) : d68178 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d51824, d68178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3962 q ha hb
    | true =>
      simp only [d51824, d68178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51825 q = 1) (hb : d57572 q = 1) : d68179 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d51825, d68179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51825, d68179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51826 q = 1) (hb : d57572 q = 1) : d68180 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d51826, d68180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51826, d68180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51827 q = 1) (hb : d57572 q = 1) : d68181 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d51827, d68181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51827, d68181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51828 q = 1) (hb : d57572 q = 1) : d68182 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d51828, d68182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51828, d68182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51829 q = 1) (hb : d57572 q = 1) : d68183 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d51829, d68183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51829, d68183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3964 (p : Pattern) (ha : d51835 p = 1) (hb : d57572 p = 1) : d68189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51830 q = 1) (hb : d57572 q = 1) : d68184 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d51830, d68184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3963 q ha hb
    | true =>
      simp only [d51830, d68184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51831 q = 1) (hb : d57572 q = 1) : d68185 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d51831, d68185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51831, d68185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51832 q = 1) (hb : d57572 q = 1) : d68186 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d51832, d68186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51832, d68186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51833 q = 1) (hb : d57572 q = 1) : d68187 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d51833, d68187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51833, d68187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51834 q = 1) (hb : d57572 q = 1) : d68188 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d51834, d68188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51834, d68188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51835 q = 1) (hb : d57572 q = 1) : d68189 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d51835, d68189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51835, d68189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3965 (p : Pattern) (ha : d51841 p = 1) (hb : d57572 p = 1) : d68195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51836 q = 1) (hb : d57572 q = 1) : d68190 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d51836, d68190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3964 q ha hb
    | true =>
      simp only [d51836, d68190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51837 q = 1) (hb : d57572 q = 1) : d68191 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d51837, d68191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51837, d68191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51838 q = 1) (hb : d57572 q = 1) : d68192 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d51838, d68192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51838, d68192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51839 q = 1) (hb : d57572 q = 1) : d68193 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d51839, d68193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51839, d68193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51840 q = 1) (hb : d57572 q = 1) : d68194 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d51840, d68194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51840, d68194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51841 q = 1) (hb : d57572 q = 1) : d68195 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d51841, d68195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51841, d68195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3966 (p : Pattern) (ha : d51847 p = 1) (hb : d57572 p = 1) : d68201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51842 q = 1) (hb : d57572 q = 1) : d68196 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d51842, d68196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3965 q ha hb
    | true =>
      simp only [d51842, d68196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51843 q = 1) (hb : d57572 q = 1) : d68197 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d51843, d68197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51843, d68197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51844 q = 1) (hb : d57572 q = 1) : d68198 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d51844, d68198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51844, d68198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51845 q = 1) (hb : d57572 q = 1) : d68199 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d51845, d68199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51845, d68199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51846 q = 1) (hb : d57572 q = 1) : d68200 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d51846, d68200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51846, d68200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51847 q = 1) (hb : d57572 q = 1) : d68201 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d51847, d68201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51847, d68201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3967 (p : Pattern) (ha : d51853 p = 1) (hb : d67923 p = 1) : d68207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51848 q = 1) (hb : d57572 q = 1) : d68202 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d51848, d68202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3966 q ha hb
    | true =>
      simp only [d51848, d68202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51849 q = 1) (hb : d57572 q = 1) : d68203 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d51849, d68203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51849, d68203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51850 q = 1) (hb : d57572 q = 1) : d68204 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d51850, d68204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51850, d68204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51851 q = 1) (hb : d67923 q = 1) : d68205 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d51851, d67923, d68205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51851, d67923, d68205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51852 q = 1) (hb : d67923 q = 1) : d68206 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d51852, d68206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51852, d68206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51853 q = 1) (hb : d67923 q = 1) : d68207 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d51853, d68207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51853, d68207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro3968 (p : Pattern) (ha : d51859 p = 1) (hb : d67924 p = 1) : d68213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51854 q = 1) (hb : d67923 q = 1) : d68208 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d51854, d68208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3967 q ha hb
    | true =>
      simp only [d51854, d68208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51855 q = 1) (hb : d67923 q = 1) : d68209 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d51855, d68209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51855, d68209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51856 q = 1) (hb : d67924 q = 1) : d68210 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d51856, d67924, d68210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51856, d67924, d68210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51857 q = 1) (hb : d67924 q = 1) : d68211 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d51857, d68211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51857, d68211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51858 q = 1) (hb : d67924 q = 1) : d68212 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d51858, d68212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51858, d68212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d51859 q = 1) (hb : d67924 q = 1) : d68213 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d51859, d68213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51859, d68213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro3969 (p : Pattern) (ha : d51865 p = 1) (hb : d67924 p = 1) : d68219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51860 q = 1) (hb : d67924 q = 1) : d68214 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d51860, d68214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3968 q ha hb
    | true =>
      simp only [d51860, d68214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51861 q = 1) (hb : d67924 q = 1) : d68215 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d51861, d68215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51861, d68215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51862 q = 1) (hb : d67924 q = 1) : d68216 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d51862, d68216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51862, d68216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51863 q = 1) (hb : d67924 q = 1) : d68217 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d51863, d68217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51863, d68217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51864 q = 1) (hb : d67924 q = 1) : d68218 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d51864, d68218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51864, d68218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51865 q = 1) (hb : d67924 q = 1) : d68219 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d51865, d68219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51865, d68219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3970 (p : Pattern) (ha : d1 p = 1) (hb : d68219 p = 1) : d68219 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d68219 q = 1) : d68219 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro3971 (p : Pattern) (ha : d53647 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3883 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3884 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3894 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3895 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
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
theorem andIntro3972 (p : Pattern) (ha : d53655 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3973 (p : Pattern) (ha : d53665 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53662, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3974 (p : Pattern) (ha : d53671 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3891 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3892 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3972 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3973 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3975 (p : Pattern) (ha : d53677 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3971 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3974 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3976 (p : Pattern) (ha : d53680 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d504, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3977 (p : Pattern) (ha : d53691 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53688, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3978 (p : Pattern) (ha : d53697 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3902 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3903 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3976 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3977 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3979 (p : Pattern) (ha : d53703 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3978 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3980 (p : Pattern) (ha : d53707 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d796, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3981 (p : Pattern) (ha : d53718 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53715, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3982 (p : Pattern) (ha : d53724 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3914 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3915 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3980 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3981 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3983 (p : Pattern) (ha : d53730 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3982 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3984 (p : Pattern) (ha : d53735 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1175, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3985 (p : Pattern) (ha : d53746 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53742 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53743, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3986 (p : Pattern) (ha : d53752 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3926 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3927 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3984 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3985 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3987 (p : Pattern) (ha : d53758 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3986 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3988 (p : Pattern) (ha : d53764 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1635 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1636, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3989 (p : Pattern) (ha : d53775 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53772, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3990 (p : Pattern) (ha : d53781 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3938 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3939 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3988 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3989 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3991 (p : Pattern) (ha : d53787 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3990 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3992 (p : Pattern) (ha : d53794 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2118 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2119, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3993 (p : Pattern) (ha : d53805 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53802, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3994 (p : Pattern) (ha : d53811 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3950 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3951 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3992 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3993 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3995 (p : Pattern) (ha : d53817 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3994 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3996 (p : Pattern) (ha : d53823 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3975 q ha hb
    | true =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3979 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3983 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3987 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3991 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3995 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3997 (p : Pattern) (ha : d53829 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3996 q ha hb
    | true =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3998 (p : Pattern) (ha : d53835 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3997 q ha hb
    | true =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3999 (p : Pattern) (ha : d53841 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3998 q ha hb
    | true =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
